# Supporting Artifact for
# "Checking 𝛿-Satisfiability of Reals with Integrals"
# by Cody Rivera, Bishnu Bhusal, Rohit Chadha, A. Prasad Sistla,
# and Mahesh Viswanathan.
# 
# Artifact by Cody Rivera and Bishnu Bhusal, 2025. 
#
# Script for getting static information about benchmarks.

import csv

from math import inf
from sexpdata import parse, car, cdr, Symbol, String, Quoted, Brackets, Parens

from benchmark_list import benchmarks

def isatom(sexp):
    return not isinstance(sexp, list) or len(sexp) == 0

def isnumber(sexp):
    return isinstance(sexp, int) or isinstance(sexp, float)

intervals = {}

def set_lower(sym, val):
    if not (sym in intervals):
        intervals[sym] = [val, inf]
    else:
        intervals[sym][0] = val

def set_upper(sym, val):
    if not (sym in intervals):
        intervals[sym] = [-inf, val]
    else:
        intervals[sym][1] = val

def get_interval_values(sexp):
    if not isatom(sexp):
        if car(sexp) == Symbol("assert"):
            asn = car(cdr(sexp))
            # we only need approximate width
            if asn[0] == Symbol("<=") or asn[0] == Symbol("<"):
                if isinstance(asn[1], Symbol) and isnumber(asn[2]):
                    set_upper(asn[1], asn[2])
                elif isinstance(asn[2], Symbol) and isnumber(asn[1]):
                    set_lower(asn[2], asn[1])
            elif asn[0] == Symbol(">=") or asn[0] == Symbol(">"):
                if isinstance(asn[1], Symbol) and isnumber(asn[2]):
                    set_lower(asn[1], asn[2])
                elif isinstance(asn[2], Symbol) and isnumber(asn[1]):
                    set_upper(asn[2], asn[1])
        else:
            get_interval_values(car(sexp))
            get_interval_values(cdr(sexp))

def count_integrals(sexp):
    if isatom(sexp):
        return 0
    else:
        if car(sexp) == Symbol("integral"):
            return 1
        else:
            return count_integrals(car(sexp)) + count_integrals(cdr(sexp))

def get_maxdepth_integrals(sexp):
    if isatom(sexp):
        return 0
    else:
        if car(sexp) == Symbol("integral"):
            return 1 + get_maxdepth_integrals(cdr(sexp))
        else:
            return max(get_maxdepth_integrals(car(sexp)), get_maxdepth_integrals(cdr(sexp)))
        
def num_vars(sexp):
    if isatom(sexp):
        return 0
    else:
        if car(sexp) == Symbol("declare-fun"):
            return 1
        elif car(sexp) == Symbol("forall"):
            return len(car(cdr(sexp))) + num_vars(cdr(cdr(sexp)))
        else:
            return num_vars(car(sexp)) + num_vars(cdr(sexp))

def avg_interval_size():
    if len(intervals) == 0:
        return "N/A"
    sum = 0.0
    for lb, ub in intervals.values():
        sum += abs(ub - lb)
    return sum / len(intervals)

def max_interval_size():
    if len(intervals) == 0:
        return "N/A"
    max = -inf
    for lb, ub in intervals.values():
        if abs(ub - lb) > max:
            max = abs(ub - lb)
    return max

rows = []
for e in benchmarks:
    file = open("int-dreal/" + e + ".smt2", "r")
    sexp = parse(file.read())
    intervals = {}
    get_interval_values(sexp)
    if Symbol("pi") in intervals:
        del intervals[Symbol("pi")] # get rid of this constant
    row = {}
    row["example"] = e
    row["num_free_vars"] = len(intervals)
    row["max_interval_size"] = max_interval_size()
    row["num_integral_terms"] = count_integrals(sexp)
    
    rows.append(row)
with open(f'results/benchmark_statistics.csv', 'w', newline='') as outfile:
    writer = csv.DictWriter(outfile, ['example', 'num_free_vars', 'max_interval_size', 'num_integral_terms'])
    writer.writeheader()
    writer.writerows(rows)
