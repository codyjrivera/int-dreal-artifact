import argparse
import csv
import os
import pyperf
import subprocess

parser = argparse.ArgumentParser(description='Benchmarking tool')

examples = ['eth_colrank_fair_00.fr',
            'eth_colrank_unfair_00.fr'
            'high_income_gender_00.fr',
            'high_income_gender_unfair_00.fr']

rows = []

args = parser.parse_args()

tests_path = os.path.join(os.getcwd(), '../dreal')

eps_list = [0.1, 0.1, 0.15, 0.15]
new_env = os.environ.copy()

benchmark_time_template = '''python3 -m pyperf command --processes=2 --values=2  --pipe=1 timeout -s 9 600 python fairProve.py -f {folder_path}/{file} -z -mi -mf -z -e {eps}'''

for index, example in enumerate(examples):
    print('We are working on ' + example)

    eps = eps_list[index]
    output = dict()

    output['test'] = example
    print(benchmark_time_template.format(file=example,
                                         folder_path=tests_path, eps=eps))

    try:
        benchmark = subprocess.run(benchmark_time_template.format(file=example,
                                                                  folder_path=tests_path, eps=eps),
                                   env=new_env,
                                   stdout=subprocess.PIPE,
                                   shell=True).stdout.decode('utf-8')

        benchmark = pyperf.BenchmarkSuite.loads(benchmark)
        benchmark = benchmark.get_benchmark('command')
        output['dreal_mean_time_usage'] = round(benchmark.mean(), 3)
        output['dreal_time_usage_unit'] = benchmark.get_unit()
    except:
        output['dreal_mean_time_usage'] = "TIMEOUT"
        output['dreal_time_usage_unit'] = "TIMEOUT"

    rows.append(output)

# rows.sort(key=lambda a: a['test'], reverse=False)

with open(f'result.csv', 'w', newline='') as outfile:
    writer = csv.DictWriter(outfile, rows[0].keys())
    writer.writeheader()
    writer.writerows(rows)
