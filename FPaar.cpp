/*
 * FPaar.cpp
 *
 * FPaar: a randomized cancellation-flip heuristic for reducing the XOR count of
 * binary matrix multiplication over GF(2). This is the reference implementation
 * accompanying the paper
 *   "FPaar: A Randomized Cancellation-Flip Framework for XOR Reduction in
 *    Binary Matrix Multiplication".
 *
 * Input:  a single binary matrix, first line "rows cols", then rows x cols
 *         space-separated 0/1 entries (row-major).
 * Output: a straight-line program (SLP), one XOR gate per line "lhs = a + b",
 *         where a,b are inputs x_i, intermediates t_k, or already-realized
 *         outputs y_i. The format matches the input generator so the circuit
 *         can be fed to a verifier unchanged.
 *
 * Algorithm (paper notation):
 *   Algorithm 2 (FPaar)  : random column permutation + Paar reuse + a flip step.
 *   Algorithm 1          : Heuristic Cancellation Flip.
 *   Definition 2         : a cancellation flip rewrites a row bit pattern
 *                          (c_i[l], c_j[l], c_new[l]) from (1,0,0)->(0,1,1) or
 *                          (0,1,0)->(1,0,1); it preserves every output's linear
 *                          expression but changes the matrix representation.
 *   Definition 3         : reduction gain Delta = #xor^Paar(P) - #xor^Paar(P');
 *                          Delta > 0 means the flip lowers Paar's XOR count.
 *
 *   Concretely each restart does:
 *     1. (Random runs only) apply a random permutation to the input columns;
 *        the very first run is deterministic (identity permutation + smallest
 *        flip-row tie-break), so the first output always equals the no-random
 *        case FPaar*.
 *     2. Repeat Paar's step: pick the column pair (c_i, c_j) with the largest
 *        overlap wt(c_i & c_j), form c_new = c_i & c_j, XOR it into c_i and
 *        c_j, and add c_new as a new intermediate column.
 *     3. After each reuse step with bestfreq > 1 (Algorithm 2), run
 *        Algorithm 1: for every row admitting a cancellation flip, evaluate
 *        the exact gain Delta by running Paar to completion on the flipped
 *        matrix, then apply the max-gain flip (random tie-break in randomized
 *        runs).
 *   The best SLP over all runs is written to OUTPUT_FILE immediately after
 *   every improving run, so terminating the process still leaves the best
 *   result found so far on disk.
 *
 * Accelerations:
 *   - Incremental CheckPaar: overlap counts wt(c_i & c_j) are held in a
 *     lower-triangular AND matrix plus a lazy max-heap. A Paar step mutates
 *     only three columns (c_i, c_j, c_new), so O(size) entries are refreshed
 *     per step instead of O(size^2).
 *   - Parallel flip verification: the exact CheckPaar of each candidate flip
 *     is distributed across FLIP_NUM_THREADS threads.
 *   - FLIP_TOP_K flip filtering: only the top-K flippable rows, ranked by a
 *     cheap row-weight proxy, are exact-checked. This is an APPROXIMATE
 *     acceleration that may lose some solution quality; K = 0 exact-checks
 *     every candidate (exact, no loss).
 *
 * Build:  g++ -O2 -o fpaar_release fpaar_release.cpp
 *         (MinGW.org GCC on Windows, or any C++11 compiler on Linux)
 */

#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <utility>
#include <cstdint>
#include <random>
#include <ctime>
#include <climits>
#include <algorithm>
#include <queue>
#include <tuple>
#if defined(_WIN32)
  #ifndef NOMINMAX
    #define NOMINMAX
  #endif
  #include <windows.h>       /* native threads: MinGW.org GCC lacks std::thread */
#else
  #include <thread>
#endif

using namespace std;

/* ===================== user-editable configuration ===================== */
#define INPUT_FILE       "AES.txt"      /* input matrix (single matrix)     */
#define OUTPUT_FILE      "AES_SLP.txt"  /* output XOR-sequence (SLP)        */
#define NUM_RESTARTS     9                 /* #randomized restarts. Run 0 is
                                              always deterministic; runs
                                              1..NUM_RESTARTS are randomized.
                                              0 = no randomization (1 run).   */
#define FLIP_NUM_THREADS 8                 /* threads for parallel flip check
                                              (<=1 -> serial)                 */
#define FLIP_TOP_K       0                 /* flip filtering: exact-check only
                                              the top-K flippable rows ranked
                                              by row weight; 0 = all rows.
                                              See the comment on HeuristicFlip
                                              for the trade-off.              */
#define SEED             0                 /* 0 = time(NULL); else fixed seed  */
/* ======================================================================== */

/* ========================= bit-vector helpers ========================== */
typedef vector<uint64_t> BitVec;   /* little-endian bit vector (length in 64-bit words) */

static inline bool getBit(const BitVec& v, int i) {
    return (v[i >> 6] >> (i & 63)) & 1ULL;
}
static inline void setBit(BitVec& v, int i, bool b) {
    if (b) v[i >> 6] |=  (1ULL << (i & 63));
    else   v[i >> 6] &= ~(1ULL << (i & 63));
}
static inline int popcnt(const BitVec& v) {
    int c = 0;
    for (size_t i = 0; i < v.size(); i++) c += __builtin_popcountll(v[i]);
    return c;
}
static inline BitVec bitXor(const BitVec& a, const BitVec& b) {
    BitVec r(a.size());
    for (size_t i = 0; i < a.size(); i++) r[i] = a[i] ^ b[i];
    return r;
}
static inline BitVec bitAnd(const BitVec& a, const BitVec& b) {
    BitVec r(a.size());
    for (size_t i = 0; i < a.size(); i++) r[i] = a[i] & b[i];
    return r;
}
/* ======================================================================== */

/* ============================ global state ============================= */
static int num_targets;            /* rows kept: popcount >= 2 (Paar's targets) */
static int num_inputs;             /* number of columns                        */
static int CWi;                    /* words per input-side vector  (num_inputs) */
static int CWt;                    /* words per target-side vector (num_targets)*/
static vector<BitVec> original_goals;  /* row representation after shrinking    */
static vector<int> rowWeight;      /* popcount of each target row (flip proxy)  */
static mt19937 rng;
static vector<int> perm, inv_perm; /* column permutation and its inverse        */
/* ======================================================================== */

/* Read a single matrix "rows cols\n<rows x cols 0/1>"; drop rows with popcount<2
 * (single-one and all-zero rows need no XOR gate, so they never affect the
 * optimization). */
static bool loadMatrix(istream& in) {
    int rows, cols;
    if (!(in >> rows >> cols)) return false;
    original_goals.clear();
    for (int i = 0; i < rows; i++) {
        BitVec row((cols + 63) / 64, 0);
        int w = 0;
        for (int j = 0; j < cols; j++) {
            int b; in >> b;
            if (b) { setBit(row, j, true); w++; }
        }
        if (w >= 2) original_goals.push_back(row);
    }
    num_targets = (int)original_goals.size();
    num_inputs  = cols;
    CWi = (num_inputs  + 63) / 64;
    CWt = (num_targets + 63) / 64;
    perm.assign(num_inputs, 0);
    inv_perm.assign(num_inputs, 0);
    rowWeight.resize(num_targets);
    for (int i = 0; i < num_targets; i++) rowWeight[i] = popcnt(original_goals[i]);
    return true;
}

/* identity permutation (deterministic first run) */
static void resetPerm() {
    for (int i = 0; i < num_inputs; i++) { perm[i] = i; inv_perm[i] = i; }
}

/* Random column permutation: new column perm[j] holds old column j. Row weight
 * is invariant under this permutation, so the precomputed rowWeight proxy stays
 * valid for every run. */
static void randomPermuteColumns(vector<BitVec>& goals) {
    for (int i = 0; i < num_inputs; i++) perm[i] = i;
    for (int i = num_inputs - 1; i > 0; i--) {
        uniform_int_distribution<int> d(0, i);
        swap(perm[i], perm[d(rng)]);
    }
    for (int i = 0; i < num_inputs; i++) inv_perm[perm[i]] = i;
    for (size_t r = 0; r < goals.size(); r++) {
        BitVec ng(CWi, 0);
        for (int j = 0; j < num_inputs; j++)
            if (getBit(goals[r], j)) setBit(ng, perm[j], true);
        goals[r] = ng;
    }
}

/* Write the best SLP to OUTPUT_FILE after every improving run, so an interrupt
 * still leaves the best result found so far on disk. */
static void writeSLP(const vector<string>& prog) {
    ofstream fout(OUTPUT_FILE);
    for (size_t i = 0; i < prog.size(); i++) fout << prog[i] << "\n";
    fout.close();
}

/* ======================================================================
 * FPaar: Paar's reuse + cancellation flips + random column restarts
 * ====================================================================== */
namespace FPaar {

    static vector<BitVec> cols;      /* cols[c] = column c (target-side bits) */
    static vector<BitVec> base;      /* base[c] = linear expression of col c (input-side bits) */
    static vector<BitVec> cur_goals; /* current (permuted) target rows */
    static vector<int> match;        /* match[c] = target realized by column c, or -1 */
    static vector<bool> achieved;    /* achieved[g] = target g already emitted */
    static vector<string> program;   /* XOR sequence "lhs = a + b" */
    static bool randomize_now;       /* false for run 0, true for randomized runs */

    /* Build the transposed view: base = identity, cols = target-side bits of
     * each input column. */
    static void buildCols(const vector<BitVec>& goals) {
        cur_goals = goals;
        cols.assign(num_inputs, BitVec(CWt, 0));
        base.assign(num_inputs, BitVec(CWi, 0));
        match.assign(num_inputs, -1);
        achieved.assign(num_targets, false);
        program.clear();
        for (int i = 0; i < num_inputs; i++) {
            setBit(base[i], i, true);
            for (int j = 0; j < num_targets; j++)
                if (getBit(goals[j], i)) setBit(cols[i], j, true);
        }
    }

    /* Name a column: a realized target -> y_i; an input -> x_{original index};
     * otherwise an intermediate t_k. */
    static string termName(int k) {
        if (k >= 0 && k < (int)match.size() && match[k] != -1)
            return "y" + to_string(match[k]);
        if (k < num_inputs) return "x" + to_string(inv_perm[k]);
        return "t" + to_string(k - num_inputs);
    }

    /* Emit the gate for the new column colsize: name it y_i if it realizes a
     * target, else a fresh intermediate t. */
    static void outputStep(int maxi, int maxj, int colsize, int step) {
        int goal = -1;
        for (int g = 0; g < num_targets; g++) {
            if (achieved[g]) continue;
            if (base[colsize] == cur_goals[g]) { goal = g; break; }
        }
        string lhs;
        if (goal >= 0) { lhs = "y" + to_string(goal); achieved[goal] = true; match[colsize] = goal; }
        else           { lhs = "t" + to_string(step); }
        program.push_back(lhs + " = " + termName(maxi) + " + " + termName(maxj));
    }

    /* ------------------------------------------------------------------
     * Incremental CheckPaar (AND matrix + lazy max-heap)
     * ------------------------------------------------------------------ */

    /* Tie-break: larger frequency first, then smaller i, then smaller j. This
     * matches the paper's lexicographic order, so the predicted gain is
     * realized by the subsequent Paar run. */
    struct LexMinCmp {
        bool operator()(const tuple<int,int,int>& a, const tuple<int,int,int>& b) const {
            if (get<0>(a) != get<0>(b)) return get<0>(a) < get<0>(b);
            if (get<1>(a) != get<1>(b)) return get<1>(a) > get<1>(b);
            return get<2>(a) > get<2>(b);
        }
    };

    /* Incremental most-frequent-pair finder. A[hi][lo] = wt(col[hi] & col[lo]);
     * a lazy max-heap holds (freq, lo, hi) entries that are validated against
     * A on pop. Paar mutates only three columns per step, so update() refreshes
     * O(size) AND entries rather than O(size^2). */
    struct IncFinder {
        vector<vector<uint16_t> > A;
        priority_queue<tuple<int,int,int>, vector<tuple<int,int,int> >, LexMinCmp> heap;

        void reset(const vector<BitVec>& col) {
            int size = (int)col.size();
            A.clear();
            A.reserve(2 * size + 1);
            for (int i = 0; i < size; i++) A.push_back(vector<uint16_t>(i, 0));
            while (!heap.empty()) heap.pop();
            for (int i = 0; i < size; i++)
                for (int j = 0; j < i; j++) {
                    int f = popcnt(bitAnd(col[i], col[j]));
                    A[i][j] = (uint16_t)f;
                    if (f > 0) heap.emplace(f, j, i);
                }
        }

        /* Pop the highest valid-frequency pair (lo, hi); false if none remain. */
        bool popBest(int& freq, int& lo, int& hi) {
            while (!heap.empty()) {
                int f  = get<0>(heap.top());
                lo = get<1>(heap.top());
                hi = get<2>(heap.top());
                heap.pop();
                if (A[hi][lo] == (uint16_t)f) { freq = f; return true; }
            }
            return false;
        }

        /* The new column ni (= size-1) and the two mutated columns maxi, maxj
         * changed; refresh their AND entries. */
        void update(const vector<BitVec>& col, int maxi, int maxj, int ni) {
            int size = (int)col.size();
            A.push_back(vector<uint16_t>(ni, 0));
            int changed[3] = { maxi, maxj, ni };
            for (int t = 0; t < 3; t++) {
                int cidx = changed[t];
                for (int k = 0; k < size; k++) {
                    if (k == cidx) continue;
                    int hi = (cidx > k) ? cidx : k;
                    int lo = (cidx > k) ? k : cidx;
                    int f = popcnt(bitAnd(col[hi], col[lo]));
                    A[hi][lo] = (uint16_t)f;
                    if (f > 0) heap.emplace(f, lo, hi);
                }
            }
        }
    };

    /* Forward declaration of flip-gain (used by the thread pool). */
    static int flipGain(int i, int maxi, int maxj, int colsize, int T1);

    /* ------------------------------------------------------------------
     * Parallel flip verification (thread pool)
     * ------------------------------------------------------------------ */
#if defined(_WIN32)
    struct FlipJob {
        const vector<int>* cand;
        vector<int>* gains;
        int maxi, maxj, colsize, T1;
        int start, stride;
    };
    static DWORD WINAPI flipWorker(LPVOID arg) {
        FlipJob* j = (FlipJob*)arg;
        int n = (int)j->gains->size();   /* gains holds exactly the (possibly top-K-truncated) list */
        for (int idx = j->start; idx < n; idx += j->stride)
            (*j->gains)[idx] = flipGain((*j->cand)[idx], j->maxi, j->maxj, j->colsize, j->T1);
        return 0;
    }
#endif

    /* Compute the exact gain of the candidate rows in parallel. `cand` and
     * `gains` are aligned; gains.size() gives the (possibly top-K-truncated)
     * number of rows to evaluate. */
    static void parallelFlipGains(const vector<int>& cand, vector<int>& gains,
                                  int maxi, int maxj, int colsize, int T1) {
        int n = (int)gains.size();
#if defined(_WIN32)
        int nt = (FLIP_NUM_THREADS > 1 && n > 1) ? min(FLIP_NUM_THREADS, n) : 1;
        if (nt > 60) nt = 60;                     /* WaitForMultipleObjects limit */
        vector<HANDLE> hd(nt);
        vector<FlipJob> jobs(nt);
        for (int t = 0; t < nt; t++) {
            jobs[t].cand = &cand; jobs[t].gains = &gains;
            jobs[t].maxi = maxi; jobs[t].maxj = maxj;
            jobs[t].colsize = colsize; jobs[t].T1 = T1;
            jobs[t].start = t; jobs[t].stride = nt;
            hd[t] = CreateThread(NULL, 0, flipWorker, &jobs[t], 0, NULL);
        }
        WaitForMultipleObjects(nt, hd.data(), TRUE, INFINITE);
        for (int t = 0; t < nt; t++) CloseHandle(hd[t]);
#else
        int nt = (FLIP_NUM_THREADS > 1 && n > 1) ? min(FLIP_NUM_THREADS, n) : 1;
        vector<thread> th;
        for (int t = 0; t < nt; t++) {
            th.push_back(thread([&, t, nt, n]() {
                for (int idx = t; idx < n; idx += nt)
                    gains[idx] = flipGain(cand[idx], maxi, maxj, colsize, T1);
            }));
        }
        for (size_t t = 0; t < th.size(); t++) th[t].join();
#endif
    }

    /* ------------------------------------------------------------------
     * Core algorithm
     * ------------------------------------------------------------------ */

    /* Run a full Paar over col (incrementally accelerated) and return its XOR
     * count = number of added columns. Taken by value so the global cols stays
     * untouched; this is the paper's CheckPaar(). */
    static int CheckPaar(vector<BitVec> col) {
        int n0 = (int)col.size();
        IncFinder finder;
        finder.reset(col);
        int size = n0;
        while (true) {
            int freq, lo, hi;
            if (!finder.popBest(freq, lo, hi)) break;
            BitVec newcol = bitAnd(col[lo], col[hi]);
            col[lo] = bitXor(newcol, col[lo]);
            col[hi] = bitXor(newcol, col[hi]);
            col.push_back(newcol);
            int ni = size;
            size++;
            finder.update(col, lo, hi, ni);
        }
        return size - n0;
    }

    /* Definition 2: whether row i admits a cancellation flip on (maxi, maxj,
     * colsize), i.e. its bit pattern is (1,0,0) or (0,1,0), or the special
     * case where the new column is a lone bit in two emptied columns. */
    static bool CancelFlip(int maxi, int maxj, int colsize, int i) {
        bool bit_k = getBit(cols[colsize], i);
        bool bit_x = getBit(bitXor(cols[maxi], cols[maxj]), i);
        if (!bit_k && bit_x) return true;                    /* (1,0,0) or (0,1,0) */
        bool maxi_zero = (popcnt(cols[maxi]) == 0);
        bool maxj_zero = (popcnt(cols[maxj]) == 0);
        bool k_one     = (popcnt(cols[colsize]) == 1);
        if (maxi_zero && maxj_zero && k_one) return true;
        return false;
    }

    /* Definition 3: exact gain of flipping row i, i.e. T1 - CheckPaar(after
     * flip). Read-only on the global cols, so it is safe across threads. */
    static int flipGain(int i, int maxi, int maxj, int colsize, int T1) {
        vector<BitVec> c = cols;
        BitVec unit(CWt, 0); setBit(unit, i, true);
        c[colsize] = bitXor(c[colsize], unit);
        c[maxi]    = bitXor(c[maxi],    unit);
        c[maxj]    = bitXor(c[maxj],    unit);
        int T2 = CheckPaar(std::move(c));
        return T1 - T2;
    }

    /* Algorithm 1 (Heuristic Cancellation Flip): evaluate every admissible
     * flip exactly, keep the max-gain ties, and apply one (random tie-break in
     * randomized runs, smallest row index otherwise). */
    static void HeuristicFlip(int maxi, int maxj, int colsize) {
        int T1 = CheckPaar(cols);

        /* collect every admissible flip row */
        vector<int> cand;
        for (int i = 0; i < num_targets; i++)
            if (CancelFlip(maxi, maxj, colsize, i)) cand.push_back(i);

        /* FLIP_TOP_K flip filtering: ranking flippable rows exactly requires one
         * CheckPaar each, which dominates the cost. Instead, only the top-K rows
         * are exact-checked, ranked by row Hamming weight descending (tie-break
         * row index ascending, deterministic). Heavier rows span more columns,
         * so a flip disturbs more AND-relations and is more likely to help; this
         * proxy is cheap (one popcount per row, precomputed once).
         * APPROXIMATION: a row below the top-K may hide a strictly better flip,
         * so a finite K may lose some solution quality. K = 0 exact-checks every
         * candidate and loses nothing. */
        int n = (int)cand.size();
        if (FLIP_TOP_K > 0 && n > FLIP_TOP_K) {
            sort(cand.begin(), cand.end(), [](int a, int b) {
                int wa = rowWeight[a], wb = rowWeight[b];
                if (wa != wb) return wa > wb;
                return a < b;
            });
            n = FLIP_TOP_K;
        }

        vector<int> gains(n, 0);
        parallelFlipGains(cand, gains, maxi, maxj, colsize, T1);

        int best = 0;
        vector<int> flips;
        for (int idx = 0; idx < n; idx++) {
            int gain = gains[idx];
            if (gain > best) { best = gain; flips.clear(); flips.push_back(cand[idx]); }
            else if (gain == best && best > 0) flips.push_back(cand[idx]);
        }

        if (best > 0 && !flips.empty()) {
            int q;
            if (randomize_now) {
                uniform_int_distribution<int> d(0, (int)flips.size() - 1);
                q = flips[d(rng)];
            } else {
                q = flips[0];          /* deterministic: smallest row among ties */
            }
            BitVec unit(CWt, 0); setBit(unit, q, true);
            cols[colsize] = bitXor(cols[colsize], unit);
            cols[maxi]    = bitXor(cols[maxi],    unit);
            cols[maxj]    = bitXor(cols[maxj],    unit);
        }
    }

    /* Algorithm 2 main loop: incrementally reuse the most frequent column pair,
     * then (if bestfreq > 1, per Algorithm 2) attempt a cancellation flip; the
     * flip is applied only when it reduces the XOR count. Return the XOR count. */
    static int runInner() {
        IncFinder finder;
        finder.reset(cols);
        int colsize = num_inputs;
        int step = 0;
        while (true) {
            int bestfreq, maxi, maxj;
            if (!finder.popBest(bestfreq, maxi, maxj)) break;

            BitVec newcol = bitAnd(cols[maxi], cols[maxj]);
            cols[maxi] = bitXor(newcol, cols[maxi]);
            cols[maxj] = bitXor(newcol, cols[maxj]);
            cols.push_back(newcol);
            match.push_back(-1);

            if (bestfreq > 1) {
                HeuristicFlip(maxi, maxj, colsize);
            }

            base.push_back(bitXor(base[maxi], base[maxj]));
            outputStep(maxi, maxj, colsize, step);

            finder.update(cols, maxi, maxj, colsize);   /* refresh {maxi, maxj, new} */

            colsize++;
            step++;
        }
        return step;
    }

    /* Top level: run 0 deterministic, runs 1..NUM_RESTARTS randomized; keep the
     * best XOR count and persist it to disk after every improvement. */
    static int run() {
        int best = INT_MAX;
        vector<string> bestprog;
        for (int r = 0; r <= NUM_RESTARTS; r++) {
            randomize_now = (r > 0);
            vector<BitVec> g = original_goals;
            if (randomize_now) randomPermuteColumns(g);
            else               resetPerm();
            buildCols(g);
            int d = runInner();
            cerr << "#XOR = " << d << (r == 0 ? "  (deterministic)" : "") << endl;
            if (d < best) {
                best = d;
                bestprog = program;
                writeSLP(bestprog);   /* persist now, so an interrupt keeps the best so far */
            }
        }
        program = bestprog;
        return best;
    }

} /* namespace FPaar */

/* ================================ main ================================ */
int main() {
    rng.seed(SEED ? SEED : (unsigned)time(NULL));

    ifstream fin(INPUT_FILE);
    if (!fin.is_open()) { cerr << "cannot open " << INPUT_FILE << endl; return 1; }
    if (!loadMatrix(fin)) { cerr << "cannot read matrix (expected: rows cols, then rows x cols of 0/1)" << endl; return 1; }
    fin.close();
    if (num_targets == 0) { cerr << "no row with weight >= 2 (no XOR needed)" << endl; return 0; }

    cerr << "FPaar: " << num_inputs << " inputs, " << num_targets
         << " targets, " << NUM_RESTARTS + 1 << " run(s)" << endl;

    int xors = FPaar::run();

    cerr << "best #XOR = " << xors << " -> " << OUTPUT_FILE << endl;
    return 0;
}
