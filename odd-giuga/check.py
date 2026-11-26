#!/usr/bin/env python3
"""Check the odd Giuga sequence directly from the definition. No dependencies.

A Giuga sequence (Borwein–Borwein–Borwein–Girgensohn 1996) is a finite increasing sequence of integers n_1 < ... < n_m
with  sum 1/n_i - 1/prod n_i  a positive integer (equivalently, each n_i divides (product of the others) - 1).
This checks that the 26 numbers in odd_giuga_sequence.txt are all odd and form a Giuga sequence of value 1.
"""
import os
import sys
from math import gcd, prod

sys.set_int_max_str_digits(0)
path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "odd_giuga_sequence.txt")
x = sorted(int(line) for line in open(path) if line.strip())
N = prod(x)
A = sum(N // v for v in x)

print(f"{len(x)} numbers; digit lengths {[len(str(v)) for v in x]}")
print("all odd and > 1:                      ", all(v % 2 == 1 and v > 1 for v in x))
print("all distinct:                          ", len(set(x)) == len(x))
print("x | (product of others) - 1, for all:  ", all((N // v - 1) % v == 0 for v in x))
print("sum 1/x - 1/prod is the integer:       ", (A - 1) // N if (A - 1) % N == 0 else "NOT AN INTEGER")
print("pairwise coprime (implied):            ", all(gcd(x[i], x[j]) == 1 for i in range(len(x)) for j in range(i + 1, len(x))))
