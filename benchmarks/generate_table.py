# Supporting Artifact for
# "Checking 𝛿-Satisfiability of Reals with Integrals"
# by Cody Rivera, Bishnu Bhusal, Rohit Chadha, A. Prasad Sistla,
# and Mahesh Viswanathan.
# 
# Artifact by Cody Rivera and Bishnu Bhusal, 2025. 
#
# Script for compiling Table 3 from other benchmarking runs.

import csv

from benchmark_list import benchmarks

int_dreal_results = {}
mathematica_results = {}
benchmark_statistics = {}

with open('results/int_dreal_results.csv', newline='') as csvfile:
    reader = csv.DictReader(csvfile)
    for row in reader:
        int_dreal_results[row['example']] = row

with open('results/mathematica_results.csv', newline='') as csvfile:
    reader = csv.DictReader(csvfile)
    for row in reader:
        mathematica_results[row['example']] = row

with open('results/benchmark_statistics.csv', newline='') as csvfile:
    reader = csv.DictReader(csvfile)
    for row in reader:
        benchmark_statistics[row['example']] = row

with open(f'results/table_3.csv', 'w', newline='') as outfile:
    header = [
        'example', 'num_free_vars', 'max_interval_size', 'num_integral_terms',
        'dreal_time', 'dreal_result', 'mathematica_time', 'mathematica_result',
        'speed_factor'
    ]
    writer = csv.DictWriter(outfile, header, restval='---')
    writer.writeheader()
    for e in benchmarks:
        row = {}
        row['example'] = e
        if e in benchmark_statistics:
            row.update(benchmark_statistics[e])
        if e in int_dreal_results:
            res = int_dreal_results[e]
            row['dreal_time'] = res['dreal_time']
            row['dreal_result'] = res['dreal_result']
            if 'delta-sat' in res['dreal_result']:
                res['dreal_result'] = 'delta_sat' # slight simplification.
        if e in mathematica_results:
            res = mathematica_results[e]
            row['mathematica_time'] = res['mathematica_time']
            row['mathematica_result'] = res['mathematica_result']
            r = res['mathematica_result']
            if not ('True' in r or 'False' in r or ("{{" in r and "}}" in r and "->" in r)):
                res['mathematica_result'] = 'indeterminate' 
        
        try:
            speedup = float(row['dreal_result']) / float(row['mathematica_result'])
            if speedup < 1:
                row['speed_factor'] = "< 1"
        except:
            row['speed_factor'] = "N/A"
        
        writer.writerow(row)
            



