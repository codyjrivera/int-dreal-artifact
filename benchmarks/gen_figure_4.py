# Supporting Artifact for
# "Checking 𝛿-Satisfiability of Reals with Integrals"
# by Cody Rivera, Bishnu Bhusal, Rohit Chadha, A. Prasad Sistla,
# and Mahesh Viswanathan.
# 
# Artifact by Cody Rivera and Bishnu Bhusal, 2025. 
#
# Benchmarking script for generating plots for Figure 4.

import csv
import matplotlib.pyplot as plt

def read_csv(file):
    fp = open(file, 'r')
    csv_reader = csv.DictReader(fp)

    return list(csv_reader)

def required_data_extractor(rows):
    triple = []
    double = []
    for row in rows:
        row['k'] = int(row['example'].split('_')[-1])
        row['eps_width'] = round(float(row['example'].split('_')[-3]) - float(row['example'].split('_')[-4]), 2)

        if row['example'].split('/')[0] == "integral_width_triple":
            triple.append(row)
        else:
            double.append(row)

    return triple, double


triple, double = required_data_extractor(
    read_csv('results/figure_4_results.csv')
)

triple_examples = {}
double_examples = {}

for row in triple:
    width = row['eps_width']

    if width not in triple_examples:
        triple_examples[width] = [row, ]
    else:
        triple_examples[width].append(row)

for row in double:
    width = row['eps_width']

    if width not in double_examples:
        double_examples[width] = [row, ]
    else:
        double_examples[width].append(row)


plt.figure()
for width in sorted(triple_examples.keys()):
    o = sorted(triple_examples[width], key=lambda row: row['k'])
    plt.plot(list(map(lambda row: int(row['k']), o)),
             list(map(lambda row: float(row['dreal_time']), o)), label=f'ε-width={width}')
    
plt.legend(loc="upper left")
plt.xlabel("$k$")
plt.ylabel("time")
plt.title('Performance')

plt.savefig(f'results/figure-4a.png')

plt.figure()
for width in sorted(double_examples.keys()):
    o = sorted(double_examples[width], key=lambda row: row['k'])
    plt.plot(list(map(lambda row: int(row['k']), o)),
             list(map(lambda row: float(row['dreal_time']), o)), label=f'ε-width={width}')
    
plt.legend(loc="upper left")
plt.xlabel("$k$")
plt.ylabel("time")
plt.title('Performance')

plt.savefig(f'results/figure-4b.png')
