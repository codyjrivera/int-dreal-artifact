# Supporting Artifact for
# "Checking 𝛿-Satisfiability of Reals with Integrals"
# by Cody Rivera, Bishnu Bhusal, Rohit Chadha, A. Prasad Sistla,
# and Mahesh Viswanathan.
# 
# Artifact by Cody Rivera and Bishnu Bhusal, 2025. 
#
# Benchmarking script for running Mathematica on Table 3 benchmarks.

import subprocess
import time
import csv
import os

from environment import mathematica_path
from benchmark_list import benchmarks

# Global parameters for running Mathematica.
benchmark_path = os.path.join(os.getcwd(), 'mathematica')
benchmark_extension = 'wl'
output_path = os.path.join(os.getcwd(), 'results')

def run_command(command, env):
    start_time = time.time()

    process = subprocess.run(
            'exec ' + command, # avoid timeout issues.
            env=env,
            stdout=subprocess.PIPE,
            timeout=600,
            shell=True)
    
    execution_time = time.time() - start_time
    return execution_time, process.stdout.decode('utf-8')

def run_multiple_times(command, env, num_times):
    total_time = 0
    valid_attempts = 0
    outputs = []
    for _ in range(num_times):
        execution_time, output = run_command(command, env)
        if execution_time is not None:
            total_time += execution_time
            valid_attempts += 1
            outputs.append(output)
    
    if valid_attempts > 0:
        average_time = total_time / valid_attempts
        return average_time, outputs
    else:
        return None, None

benchmark_time_template = '''{engine} {folder_path}/{file}.{extension}'''
rows = []

for example in benchmarks:
    output = dict()

    output['example'] = example

    command = benchmark_time_template.format(
        engine=mathematica_path, file=example, extension=benchmark_extension,
        folder_path=benchmark_path
    )

    print(command)

    try:
        new_env = os.environ.copy()
        mean_time, outputs = run_multiple_times(command, new_env, 3)
        output['mathematica_time'] = mean_time
        output['mathematica_result'] = outputs[0]

        print(f"Mean running time: {mean_time:.4f}")
        print(f"Output: {outputs[0]}")
    except:
        output['mathematica_time'] = "TIMEOUT"
        output['mathematica_result'] = "N/A"

        print("TIMEOUT")

    rows.append(output)

with open(output_path + '/mathematica_results.csv', 'w', newline='') as outfile:
    writer = csv.DictWriter(outfile, ['example', 'mathematica_time', 'mathematica_result'])
    writer.writeheader()
    writer.writerows(rows)
