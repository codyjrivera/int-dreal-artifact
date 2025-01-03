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

try:
    with open('results/int_dreal_results.csv', newline='') as csvfile:
        reader = csv.DictReader(csvfile)
        for row in reader:
            int_dreal_results[row['example']] = row
except:
    pass

try:
    with open('results/mathematica_results.csv', newline='') as csvfile:
        reader = csv.DictReader(csvfile)
        for row in reader:
            mathematica_results[row['example']] = row
except:
    pass

try:
    with open('results/benchmark_statistics.csv', newline='') as csvfile:
        reader = csv.DictReader(csvfile)
        for row in reader:
            benchmark_statistics[row['example']] = row
except:
    pass

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
            row['dreal_time'] = f'{float(res["dreal_time"]):.3f}'
            row['dreal_result'] = res["dreal_result"]
            if 'unsat' in res['dreal_result']:
                row['dreal_result'] = 'unsat'
            elif 'delta-sat' in res['dreal_result']:
                row['dreal_result'] = '𝛿-sat'
            else:
                row['dreal_result'] = 'indeterminate'
            
        if e in mathematica_results:
            res = mathematica_results[e]
            row['mathematica_time'] = f'{float(res["mathematica_time"]):.3f}'
            row['mathematica_result'] = res["mathematica_result"]
            r = res['mathematica_result']
            if 'True' in r:
                row['mathematica_result'] = 'True'
            elif 'False' in r:
                row['mathematica_result'] = 'False'
            elif "{{" in r and "}}" in r and "->" in r:
                row['mathematica_result'] = r.split('\n')[0]
            else:
                row['mathematica_result'] = 'indeterminate'
        
        try:
            speedup = float(row['mathematica_time']) / float(row['dreal_time'])
            if speedup < 1:
                row['speed_factor'] = "<1"
            else:
                row['speed_factor'] = round(speedup)
        except:
            row['speed_factor'] = "N/A"
        
        writer.writerow(row)
            



