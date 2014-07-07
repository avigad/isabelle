#!/usr/bin/python

from math import sqrt
import numpy as np
from scipy import special

def Binomial(N, p, n):
  return special.binom(N, n) * p**n * (1 - p)**(N - n)


def write_binomial(name, N, p = 0.5):
  # write a normalized binomal distribution
  sigma = sqrt(N) / 2
  with open(name, "w") as f:
    for n in range(0, N + 1):
      print >> f, "%0.4f  %0.5f" % ((float(n) - float(N) / 2) / sigma, Binomial(N, p, n) * sigma)

for N in [2, 8, 32, 128, 512]:
  write_binomial("binomial-%i.dat" % N, N)


