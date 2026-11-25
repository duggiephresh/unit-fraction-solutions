#!/usr/bin/env python3
"""Check the odd solution of Znám's problem directly from the definition. No dependencies.

Znám's problem: integers x_1..x_k > 1 such that each x_i is a PROPER divisor of (prod_{j != i} x_j) + 1,
i.e. x_i divides it and x_i != it. This file checks that the 24 numbers in odd_znam_solution.txt are all odd and
satisfy that condition.
"""
import os
import sys
from math import gcd, prod

sys.set_int_max_str_digits(0)
path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "odd_znam_solution.txt")
x = [int(line) for line in open(path) if line.strip()]
N = prod(x)

print(f"{len(x)} numbers; digit lengths {[len(str(v)) for v in x]}")
print("all odd and > 1:                    ", all(v % 2 == 1 and v > 1 for v in x))
print("all distinct:                        ", len(set(x)) == len(x))
print("x | (product of others) + 1, for all:", all((N // v + 1) % v == 0 for v in x))
print("x != (product of others) + 1 (proper):", all(v != N // v + 1 for v in x))
print("pairwise coprime (implied):          ", all(gcd(x[i], x[j]) == 1 for i in range(len(x)) for j in range(i + 1, len(x))))
