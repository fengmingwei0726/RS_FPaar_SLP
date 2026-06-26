# FPaar: Experimental Data and Source Code

This repository contains the experimental data and source code for the paper:

> **FPaar: A Randomized Bit-Flip Framework for XOR Reduction in Binary Matrix Multiplication**  

## Repository Structure

** HDFS_RS(10,4) **/ # 1000 optimized implementations for RS(10,4) decoding matrices from HDFS
├── ISA-L_encode/ # Optimized results for 9 RS encoding matrices with different parameters from ISA-L library
├── matrices_32-256_size/ # Cryptographic (32,64) and random (128,256) matrices
├── RS(10,4)_dec_matrices.txt # All 1001 RS(10,4) decoding matrices
└── RS(10,4)_compare_SLP.txt # XOR count comparison(Paar, RePair, XorRePair, and FPaar) on all 1002 matrices
