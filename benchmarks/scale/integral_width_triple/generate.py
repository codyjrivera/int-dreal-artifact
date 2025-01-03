# import argparse

f = 'svt_gauss_00.smt2'


def read_file_as_string(file_path):
    try:
        with open(file_path, 'r') as file:
            file_content = file.read()
        return file_content
    except FileNotFoundError:
        print(f"File not found: {file_path}")
    except Exception as e:
        print(f"An error occurred: {e}")

def save_string_to_file(file_path, content):
    try:
        with open(file_path, 'w') as file:
            file.write(content)
        print(f"File '{file_path}' saved successfully.")
    except Exception as e:
        print(f"An error occurred: {e}")

def get_file_name(f):
    return f.split('/')[-1].split('.')[0]

# parser = argparse.ArgumentParser(description='Triple Integral tool')

# parser.add_argument('-k', nargs=3, required=True)

# parser.add_argument('-eps', nargs=3, required=True)

# parser.add_argument('-f', required=True)

# args = parser.parse_args()

file_content = read_file_as_string(f)

eps_lower_match = '(assert (>= eps 0.1))'
eps_upper_match = '(assert (<= eps 1))'
k1_match = '(assert (= k 200))'
k2_match = '(assert (= k2 228))'

eps_lower_template = '(assert (>= eps {val:.2f}))'
eps_upper_template = '(assert (<= eps {val:.2f}))'
k1_template = '(assert (= k {val}))'
k2_template = '(assert (= k2 {val}))'

file_name = get_file_name(f)
# print(file_content)
# print(args.k)

eps = [0.1, 0.9, 0.2]
k = [1, 5, 1]

eps_factor = float(eps[2])
eps_lower = float(eps[0])
eps_upper = float(eps[1])
for k in range(int(k[0]), int(k[1]), int(k[2])):
    for multiplier in range(1,  int((eps_upper - eps_lower )/ eps_factor) + 1):

        new_eps_upper = eps_lower + eps_factor * multiplier
        new_file_content = file_content.replace(eps_lower_match, eps_lower_template.format(val=eps_lower))
        new_file_content = new_file_content.replace(eps_upper_match, eps_upper_template.format(val=new_eps_upper))
        new_file_content = new_file_content.replace(k1_match, k1_template.format(val=k))
        new_file_content = new_file_content.replace(k2_match, k2_template.format(val=k))

        save_string_to_file('{file}_eps_{lower:.2f}_{upper:.2f}_k_{k}.smt2'.format(
            file=file_name, 
            lower=eps_lower, 
            upper=new_eps_upper, 
            k=k), 
        new_file_content)