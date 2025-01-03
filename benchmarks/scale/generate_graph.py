from collections import defaultdict

import matplotlib.pyplot as plt
import csv

# plt.rcParams['text.usetex'] = True


def read_csv(file):
    fp = open(file, 'r+')
    csv_reader = csv.DictReader(fp)

    return list(csv_reader)


def required_data_extractor(rows):
    data = {4: [], 5: [], 3: [], 1: []}
    for row in rows:
        type_ = int(row['test'].split('_')[3])

        data[type_].append({
            'var': int(row['test'].split('_')[-1]) + 1,
            'time': float(row['time(32)'])
        })

    return data


data = required_data_extractor(read_csv('scaling_results.csv'))



for type_ in data:
    plt.figure()

    plt.plot(list(map(lambda row: int(row['var']), data[type_])),
             list(map(lambda row: float(row['time']), data[type_])), label=f'type={type_}')
    plt.legend(loc="upper left")
    plt.xlabel("number of vars")
    # plt.xlim(0, int(n_box_rows[-1]['n']))

    plt.ylabel("time")
    plt.title('Performance')

    plt.savefig(f'./plots-type-{type_}.png')