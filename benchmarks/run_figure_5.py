# Supporting Artifact for
# "Checking 𝛿-Satisfiability of Reals with Integrals"
# by Cody Rivera, Bishnu Bhusal, Rohit Chadha, A. Prasad Sistla,
# and Mahesh Viswanathan.
# 
# Artifact by Cody Rivera and Bishnu Bhusal, 2025. 
#
# Benchmarking script for generating results for Figure 5.

import subprocess
import time
import csv
import os

from environment import int_dreal_path

# Global parameters for running ∫dReal.
precision = "32"
prune_width = "0.1"

benchmark_path = os.path.join(os.getcwd(), 'scale')
benchmark_extension = 'smt2'
output_path = os.path.join(os.getcwd(), 'results')

# Benchmark list
benchmarks = ["num_variables/scale_vars_var_" + str(k) for k in range(1, 100)]

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
        engine=int_dreal_path, file=example, extension=benchmark_extension,
        folder_path=benchmark_path
    )

    print(command)

    try:
        new_env = os.environ.copy()

        new_env["ARB_PRECISION"] = precision
        new_env["MAX_PRUNE_WIDTH"] = prune_width

        mean_time, outputs = run_multiple_times(command, new_env, 3)
        output['dreal_time'] = mean_time
        output['dreal_result'] = outputs[0]
        print(f"Mean running time: {mean_time:.4f}")
        print(f"Output: {outputs[0]}")
    except:
        output['dreal_time'] = "TIMEOUT"
        output['dreal_result'] = "N/A"

        print(f"TIMEOUT")
    print('----------------------------------------------------------')

    rows.append(output)

with open(output_path + '/figure_5_results.csv', 'w', newline='') as outfile:
    writer = csv.DictWriter(outfile, ['example', 'dreal_time', 'dreal_result'])
    writer.writeheader()
    writer.writerows(rows)
