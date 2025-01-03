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
    for row in rows:
        data.append({
            'var': int(row['example'].split('_')[4]),
            'time': float(row['dreal_time'])
        })
    return data

data = required_data_extractor(read_csv('results/figure_5_results.csv'))


# Plot Figure 5a.
plt.figure()

plt.plot(list(map(lambda row: int(row['var']), data)),
            list(map(lambda row: float(row['time']), data)))
#plt.legend(loc="upper left")
plt.xlabel("number of vars")
# plt.xlim(0, int(n_box_rows[-1]['n']))

plt.ylabel("time")
plt.title('Performance')

plt.savefig(f'results/figure-5a.png')

# Plot Figure 5b.
plt.figure()

plt.plot(list(map(lambda row: int(row['var']), data)),
            list(map(lambda row: float(row['time']), data)))
#plt.legend(loc="upper left")
plt.xlabel("number of vars")
plt.ylim(0, 0.14)

plt.ylabel("time")
plt.title('Performance')

plt.savefig(f'results/figure-5b.png')