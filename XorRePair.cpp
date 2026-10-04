/*
 * XorRePair.cpp
 *
 * Short auxiliary tool for the FPaar paper submission. Reads a single binary
 * matrix (same format as fpaar_release.cpp: first line "rows cols", then
 * rows x cols of space-separated 0/1) and prints the three baseline XOR counts:
 *
 *   d-XOR     : direct XOR count  = sum over rows of max(0, weight - 1)
 *   Paar      : Paar's greedy column-pair reuse [Paar97], deterministic
 *   XorRePair : Uezato et al. SC'21 [Uezato21]; only the paper's entry point
 *               run_xor_repair_reverse(LexSmall) is kept.
 *
 * All three metrics match the paper: d-XOR counts one XOR per 1 beyond the
 * first in each row; Paar and XorRePair return the number of XOR gates their
 * greedy SLP uses.
 *
 * Build:  g++ -O2 -o baseline_counts baseline_counts.cpp
 *         (MinGW.org GCC on Windows, or any C++11 compiler on Linux)
 */

#include <iostream>
#include <fstream>
#include <vector>
#include <cstdint>
using namespace std;

#define INPUT_FILE "AES.txt"   /* input matrix (single matrix) */

typedef vector<uint64_t> BitVec;  /* little-endian bit vector (length in 64-bit words) */

/* ========================= bit-vector helpers ========================= */
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
static inline int nwords(int bits) { return (bits + 63) / 64; }
/* ===================================================================== */

/* Read "rows cols" then rows x cols of 0/1. Drop rows with weight < 2 (they
 * need no XOR gate); d-XOR sums (weight - 1) over the kept rows. */
static bool loadMatrix(istream& in, vector<BitVec>& goals, int& dxor, int& ncols) {
    int rows, cols;
    if (!(in >> rows >> cols)) return false;
    ncols = cols;
    goals.clear();
    dxor = 0;
    for (int i = 0; i < rows; i++) {
        BitVec row(nwords(cols), 0);
        int w = 0;
        for (int j = 0; j < cols; j++) {
            int b; in >> b;
            if (b) { setBit(row, j, true); w++; }
        }
        if (w >= 2) { goals.push_back(row); dxor += w - 1; }
    }
    return true;
}

/* ============================ Paar's algorithm ============================
 * Column-based greedy: repeatedly XOR the most-overlapping column pair into a
 * new intermediate column. Deterministic lexicographic tie-break (smallest
 * (i,j) on equal overlap). Returns the XOR count. */
static int paarCount(const vector<BitVec>& goals, int ncols) {
    int m = (int)goals.size();
    vector<BitVec> cols(ncols, BitVec(nwords(m), 0));
    for (int j = 0; j < ncols; j++)
        for (int i = 0; i < m; i++)
            if (getBit(goals[i], j)) setBit(cols[j], i, true);

    int size = ncols;
    while (true) {
        int bestfreq = 0, bi = -1, bj = -1;
        for (int i = 0; i < size; i++)
            for (int j = i + 1; j < size; j++) {
                int f = popcnt(bitAnd(cols[i], cols[j]));
                if (f > bestfreq) { bestfreq = f; bi = i; bj = j; }
            }
        if (bestfreq == 0) break;
        BitVec nc = bitAnd(cols[bi], cols[bj]);
        cols[bi] = bitXor(cols[bi], nc);
        cols[bj] = bitXor(cols[bj], nc);
        cols.push_back(nc);
        size++;
    }
    return size - ncols;
}

/* =========================== XorRePair (SC'21) ============================
 * Row-based greedy: rebuild each goal with existing variables (this is where
 * XOR cancellation comes from), then pair the two most co-occurring terms into
 * a new variable. Only the paper's entry run_xor_repair_reverse(LexSmall) is
 * kept, i.e. rebuild iterates variables in reverse order and pair ties pick
 * the largest (i,j). Returns the XOR count. */
static int xorrepairCount(const vector<BitVec>& goals, int nconst) {
    int CW = nwords(nconst);
    vector<BitVec> slp  = goals;   /* remaining goals (width CW)             */
    vector<BitVec> prog = goals;   /* current syntax, width grows with vars  */
    vector<BitVec> val;            /* valuation of each added variable (CW)  */
    int nvars = 0, defs = 0;

    while (true) {
        int nterms = nconst + nvars;

        /* Step 1: rebuild each goal in reverse order, keep if shorter */
        for (int r = 0; r < (int)slp.size(); r++) {
            BitVec depends(nwords(nterms), 0);
            BitVec rest = slp[r];
            while (true) {
                int which = -1, cur_min = popcnt(rest);
                for (int v = nvars - 1; v >= 0; v--) {
                    int d = 0;
                    for (int w = 0; w < CW; w++) d += __builtin_popcountll(val[v][w] ^ rest[w]);
                    if (d < cur_min) { which = v; cur_min = d; }
                }
                if (which >= 0) {
                    setBit(depends, nconst + which, true);
                    rest = bitXor(rest, val[which]);
                } else {
                    for (int i = 0; i < nconst; i++)
                        if (getBit(rest, i)) setBit(depends, i, true);
                    break;
                }
            }
            if (popcnt(depends) < popcnt(prog[r])) prog[r] = depends;
        }

        /* Step 2: count co-occurrences of each term pair, keep the max
         * (LexSmall: on ties keep the largest (i,j), i.e. the last seen) */
        int count_max = 0, bi = -1, bj = -1;
        for (int i = 0; i < nterms; i++)
            for (int j = i + 1; j < nterms; j++) {
                int cnt = 0;
                for (int r = 0; r < (int)slp.size(); r++)
                    if (getBit(prog[r], i) && getBit(prog[r], j)) cnt++;
                if (cnt > count_max) { count_max = cnt; bi = i; bj = j; }
                else if (cnt == count_max) { bi = i; bj = j; }
            }
        if (count_max == 0) return defs;   /* no reusable pair remains */

        /* add a new variable = term(bi) XOR term(bj) */
        BitVec new_val(CW, 0);
        if (bi < nconst) setBit(new_val, bi, true); else new_val = bitXor(new_val, val[bi - nconst]);
        if (bj < nconst) setBit(new_val, bj, true); else new_val = bitXor(new_val, val[bj - nconst]);

        nvars++;
        int PW = nwords(nconst + nvars);
        for (auto& p : prog) p.resize(PW, 0);
        int v = nconst + defs;
        for (auto& p : prog)
            if (getBit(p, bi) && getBit(p, bj)) {
                setBit(p, bi, false); setBit(p, bj, false); setBit(p, v, true);
            }
        val.push_back(new_val);
        defs++;

        /* drop a goal now equal to the new variable */
        for (int r = (int)slp.size() - 1; r >= 0; r--)
            if (slp[r] == new_val) {
                slp[r]  = slp.back();  slp.pop_back();
                prog[r] = prog.back(); prog.pop_back();
                break;
            }
        if (slp.empty()) return defs;
    }
}

/* ================================ main ================================ */
int main() {
    ifstream fin(INPUT_FILE);
    if (!fin.is_open()) { cerr << "cannot open " << INPUT_FILE << endl; return 1; }

    vector<BitVec> goals;
    int dxor = 0, ncols = 0;
    if (!loadMatrix(fin, goals, dxor, ncols)) {
        cerr << "cannot read matrix (expected: rows cols, then rows x cols of 0/1)" << endl;
        return 1;
    }
    fin.close();
    if (goals.empty()) { cerr << "no row with weight >= 2" << endl; return 0; }

    cout << "d-XOR     = " << dxor << endl;
    cout << "Paar      = " << paarCount(goals, ncols) << endl;
    cout << "XorRePair = " << xorrepairCount(goals, ncols) << endl;
    return 0;
}
