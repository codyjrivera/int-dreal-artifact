# Supporting Artifact for
# "Checking 𝛿-Satisfiability of Reals with Integrals"
# by Cody Rivera, Bishnu Bhusal, Rohit Chadha, A. Prasad Sistla,
# and Mahesh Viswanathan.
# 
# Artifact by Cody Rivera and Bishnu Bhusal, 2025. 
#
# Benchmarking script for generating plots for Figure 5.

import csv

import matplotlib.pyplot as plt

def read_csv(file):
    fp = open(file, 'r')
    csv_reader = csv.DictReader(fp)

    return list(csv_reader)

def required_data_extractor(rows):
    data = []
    data_nested = []
    for row in rows:
        if row['example'].split('/')[0] == "num_integrals":
            data.append({
                'var': int(row['example'].split('_')[4]),
                'time': float(row['dreal_time'])
            })
        else:
            data_nested.append({
                'var': int(row['example'].split('_')[6]),
                'time': float(row['dreal_time'])
            })
    return data, data_nested

data, data_nested = required_data_extractor(read_csv('results/figure_6_results.csv'))

# Plot Figure 6a.
plt.figure()

plt.plot(list(map(lambda row: int(row['var']), data)),
            list(map(lambda row: float(row['time']), data)))
#plt.legend(loc="upper left")
plt.xlabel("number of integrals")
# plt.xlim(0, int(n_box_rows[-1]['n']))

plt.ylabel("time")
plt.title('Performance')

plt.savefig(f'results/figure-6a.png')

# Plot Figure 6b.
plt.figure()

plt.plot(list(map(lambda row: int(row['var']), data_nested)),
            list(map(lambda row: float(row['time']), data_nested)))
#plt.legend(loc="upper left")
plt.xlabel("number of integrals")

plt.ylabel("time")
plt.title('Performance')

plt.savefig(f'results/figure-6b.png')