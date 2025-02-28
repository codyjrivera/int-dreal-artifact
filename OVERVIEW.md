# Supporting Artifact for "Checking 𝛿-Satisfiability of Reals with Integrals"
by Cody Rivera, Bishnu Bhusal, Rohit Chadha, A. Prasad Sistla,
and Mahesh Viswanathan.

Artifact by Cody Rivera and Bishnu Bhusal, Version 2.0, 2025.
(Revisions: Add license and clarify that the results in the final paper
use the artifact as it stands).

## Introduction
This is the supporting artifact for "Checking 𝛿-Satisfiability of Reals with 
Integrals", a paper which extends the framework of 𝛿-decision procedures to 
handle integrals of custom real-valued functions. We provide an implementation
of this extended decision procedure, ∫dReal. We also provide a benchmark suite
written in ∫dReal's input language, as well as equivalent benchmarks in 
Wolfram language or FairSquare's input language, where appropriate.

Our paper's claims follow:
1. We can extend the framework of 𝛿-decision procedures to handle integration.

Our artifact supports this by providing an implementation: ∫dReal, an
extension of dReal version 4.

2. We can apply ∫dReal to queries in synthesis and verification
related to differential privacy and algorithmic fairness.

Our artifact contains queries corresponding to synthesis and verification
problems in these domains. We also provide a correspondence between the
queries described in the paper and queries in our artifact.

3. ∫dReal demonstrates favorable performance on many of the queries we
evaluate, including when compared to Mathematica and FairSquare, where
appropriate.

Our artifact contains scripts allowing users to run ∫dReal on our
benchmark suite and record run times. Our artifact also contains scripts
allowing users to run equivalent queries on Mathematica and FairSquare
as a point of comparison.

3. ∫dReal demonstrates scalability properties, on different aspects of 
input queries, as discussed in Section 7.3 of the paper.

Our artifact contains queries and scripts allowing users to replicate the
observations we describe in Section 7.3.

## Hardware Dependencies
We have tested this artifact on the following machine configuations
- An x86-64 laptop with a 3.8 GHz AMD® Ryzen 7 Pro 7840HS processor and 32 GB 
  of RAM, running Ubuntu 24.04.

## Getting Started
We start by providing users with a Docker container with ∫dReal 
and our benchmark suite. There are two ways of running this container: use 
our prebuilt Docker image, or build a new Docker image.

### Use an Existing Docker Image
The provided image `int-dreal-image.tar` supplies an Ubuntu 22.04 environment 
and the software to run the benchmarks. Here are the directions to use
this image:
1. Install Docker Engine. See [here](https://docs.docker.com/engine/install/)
   for instructions.
2. Run `docker load -i int-dreal-image.tar` to load the extracted image into
   Docker.
3. To obtain an interactive shell for the container `int-dreal-image`, run
   the following command:
```
docker run -it --mount type=bind,src="$(pwd)/benchmarks",target=/home/ubuntu/int-dreal-artifact/benchmarks \
       int-dreal-image /bin/bash
```
   (the `--mount` option allows you to copy files to the host machine).

### Build a New Docker Image (~15 min)
Below are instructions for building a new Docker image.
1. Install Docker Engine. See [here](https://docs.docker.com/engine/install/)
   for instructions.
2. In the root directory of this artifact, run 
   `docker build -t int-dreal-image .` to build the image.
3. To obtain an interactive shell for the container `int-dreal-image`, run
   the following command:
```
docker run -it --mount type=bind,src="$(pwd)/benchmarks",target=/home/ubuntu/int-dreal-artifact/benchmarks \
       int-dreal-image /bin/bash
```
   (the `--mount` option allows you to copy files to the host machine).

### Run a Set of Getting Started Benchmarks (~5 min)
In order to ensure the user's image is set up correctly, we offer a script
that runs a subset of our benchmark suite on ∫dReal. The notable exclusions
are `eth_colrank_unfair_01`, `svt_gauss_sat_00`, and `gauss_forall_00`.
These benchmarks take more than 1 minute to run on the Ubuntu 24.04 laptop
used to develop the artifact.

To run these benchmarks, perform the following steps, starting from the
top-level directory inside the container:

1. Run `cd benchmarks`.
2. Run `python3 getting_started_benchmark.py`. 

The results should appear in a table at
`benchmarks/results/getting_started_results.csv`. A sample output
should appear at `benchmarks/sample-results/getting_started_results.csv`.

Comparing the results in `getting_started_results.csv` with Table 3, the
performance trends are similar.

## Step by Step Instructions
We detail how one can use our artifact to show our paper's claims in this
section.

### Support for Claim 1 (can add integration to 𝛿-decision procedures)
Our artifact provides an extended implementation of dReal 4 and IBEX, the
underlying constraint programming library, to support adding integration
to 𝛿-decision procedures. The most relevant files in our artifact implementing
our extensions include the following:

* `dreal4/dreal/solver`:
    - `expression_evaluator.{cc, h}`.
    - `integral_expression_evaluator.{cc, h}`
* `ibex-lib/src/function`:
    - `ibex_Eval.{cpp, h}`
    - `ibex_HC4Revise.{cpp, h}`
    - `ibex_IntegralEval.{cpp, h}`

### Support for Claim 2 (can use ∫dReal in verification and synthesis)
Our paper describes a variety of case studies using ∫dReal, and our
artifact contains the queries corresponding to them. We explicitly state
this correspondance in the file `benchmarks/CASE_STUDIES.md`.

We implement our benchmark suite in both ∫dReal's input language and Wolfram
language. The former implementation can be found in `benchmarks/int-dreal`,
while the latter implementation can be found in `benchmarks/mathematica`.

### Support for Claim 3 (performance evaluation of ∫dReal and other tools)
The paper supports Claim 3 primarily through Table 3. Parts 1-4 will walk
users through how to generate data on this table, and part 5 will allow users
to evaluate the relevant algorithmic fairness benchmarks on FairSquare.

#### Claim 3, Part 1 (running ∫dReal on benchmarks, ~1 hr)
We start by running ∫dReal on our entire benchmark suite (minus the 
scalability experiments).

To run these benchmarks, perform the following steps, starting from the
top-level directory inside the container:

1. Run `cd benchmarks`.
2. Run `python3 int_dreal_benchmark.py`. 

The results should appear in a table at
`benchmarks/results/int_dreal_results.csv`. A sample output
should appear at `benchmarks/sample-results/int_dreal_results.csv`.

#### Claim 3, Part 2 (running Mathematica on benchmarks, ~40 min)
Since Wolfram Mathematica is proprietary software, we do not include it in
a Docker image. However, we do provide equivalent benchmarks and a
script that can be used to run them. 

We intend for the Python script provided not to rely on external Python
packages. However, users may need to modify the file `environment.py` to
provide the proper command to run Mathematica in batch mode.

To run these benchmarks, perform the following steps, starting from the
top-level directory:

1. Run `cd benchmarks`.
2. Run `python3 mathematica_benchmark.py`

The results should appear in a table at
`benchmarks/results/mathematica_results.csv`. A sample output
should appear at `benchmarks/sample-results/mathematica_results.csv`.
The sample output was derived from an author's Ubuntu 24.04 x86_64 laptop,
running Mathematica 13.3.1, not containerized.

#### Claim 3, Part 3 (getting auxiliary query information)
Much information about our queries in Table 3 is easily derivable
automatically. We provide a script to obtain this information.

To run this script, perform the following steps, starting from the
top-level directory inside the container:

1. Run `cd benchmarks`.
2. Run `python3 benchmark_statistics.py`. 

The results should appear in a table at
`benchmarks/results/benchmark_statistics.csv`. A sample output
should appear at `benchmarks/sample-results/benchmark_statistics.csv`.

#### Claim 3, Part 4 (generating Table 3)
In Parts 1-3, we obtained the information necessary for constructing 
Table 3. Here is the procedure for generating this table.

The following files are needed for the process to be
successful:
* `benchmarks/results/benchmark_statistics.csv`
* `benchmarks/results/int_dreal_results.csv`
* `benchmarks/results/mathematica_results.csv`

To generate the table, perform the following steps, starting from the
top-level directory inside the container:

1. Run `cd benchmarks`.
2. Run `python3 generate_table.py`.

The results should appear in a table at
`benchmarks/results/table_3.csv`. A sample output
should appear at `benchmarks/sample-results/table_3.csv`.

When comparing `table_3.csv` and Table 3 in the paper submission, there is a
very strong correspondence between the results. The numbers reported in the
paper and the numbers reported by the artifact formerly were slightly different,
(see V1 of our artifact: https://doi.org/10.5281/zenodo.14593603), but they
have been reconciled in the final version of the paper.

#### Claim 3, Part 5 (running FairSquare on benchmarks, ~5 min)
For a subset of our benchmarks related to algorithmic fairness, including
`high_inc_gd_00`, `high_inc_gd_unfair_00`, `eth_colrank_fair_00`, and
`eth_colrank_unfair_00`, we evaluate the fairness of the program from which
we obtain our queries using FairSquare. The benchmarks can be seen in the 
directory `fairsquare/dreal`. We provide a separate Docker image for running
FairSquare benchmarks. To run these benchmarks, perform the following steps, 
starting from the top-level directory and outside of a container:

1. Run `cd fairsquare`.
2. Run `docker load -i fairsquare-image.tar` to load the FairSquare image.
3. Run `docker run -it fairsquare-image /bin/bash` to enter an interactive
   shell.
4. Run `cd src`.
5. Run `python3 benchmark.py` to run FairSquare on the appropriate
   benchmarks.
6. Run `cat result.csv` to output the results.

The results corresponding to Table 4 should be in the file `result.csv`. An
example `result.csv` can be seen in the file `fairsquare/example-result.csv`
(relative to the top-level directory of the *artifact*).

### Support for Claim 4 (scalability evaluation of ∫dReal)
In Section 7.3 of the paper submission, we evaluate the scalability of ∫dReal
with respect to different aspects of the input. We detail how to replicate the
experiments described in the section as well as the corresponding figures.

#### Claim 4, Part 1 (scalability with respect to integral endpoints
#### and interval width, ~50 min)
In Figure 4, we evaluate the scalability of ∫dReal with respect to interval
width of existentially-quantified variables, and width between integral
endpoints. We evaluate this on three-deep and equivalent two-deep nested 
integrals. The three-deep integral benchmarks can be seen at
`benchmarks/scale/integral_width_triple`, and the two-deep benchmarks can be
seen at `bencmarks/scale/integral_width_double`.

To run these benchmarks, perform the following steps, starting from the
top-level directory in the container:

1. Run `cd benchmarks`.
2. Run `python3 run_figure_4.py`

The results should appear in a table at
`benchmarks/results/figure_4_results.csv`. A sample output
should appear at `benchmarks/sample-results/figure_4_results.csv`.

To generate the corresponding figures, run the following additional
command:

3. Run `python3 gen_figure_4.py`

The figure should appear as the files
`benchmarks/results/figure-4{a, b}.png`. Sample outputs should
appear at `benchmarks/sample-results/figure-4{a, b}.png`.

#### Claim 4, Part 2 (scalability with respect to number of free vars, ~10 min)
In Figure 5, we evaluate the scalability of ∫dReal with respect to the
number of existentially-quantified variables. The benchmarks can be
seen at `benchmarks/scale/num_variables`.

To run these benchmarks, perform the following steps, starting from the
top-level directory in the container:

1. Run `cd benchmarks`.
2. Run `python3 run_figure_5.py`

The results should appear in a table at
`benchmarks/results/figure_5_results.csv`. A sample output
should appear at `benchmarks/sample-results/figure_5_results.csv`.

To generate the corresponding figures, run the following additional
command:

3. Run `python3 gen_figure_5.py`

The figure should appear as the files
`benchmarks/results/figure-5{a, b}.png`. Sample outputs should
appear at `benchmarks/sample-results/figure-5{a, b}.png`.

#### Claim 4, Part 3 (scalability with respect to number of integral terms, ~10 min)
In Figure 6, we evaluate the scalability of ∫dReal with respect to the
number of integral terms. A version evaluating non-nested integrals can be
seen at `benchmarks/scale/num_integrals`, and ditto with nested integrals
at `benchmarks/scale/num_integrals_nested`.

To run these benchmarks, perform the following steps, starting from the
top-level directory in the container:

1. Run `cd benchmarks`.
2. Run `python3 run_figure_6.py`

The results should appear in a table at
`benchmarks/results/figure_6_results.csv`. A sample output
should appear at `benchmarks/sample-results/figure_6_results.csv`.

To generate the corresponding figures, run the following additional
command:

3. Run `python3 gen_figure_6.py`

The figure should appear as the files
`benchmarks/results/figure-6{a, b}.png`. Sample outputs should
appear at `benchmarks/sample-results/figure-6{a, b}.png`.

## Reusability Guide
The reusability of our artifact comprises the ability to write new queries
in the SMT-LIB based input language of ∫dReal, and evaluate them. Our Docker
image, if used according to our instructions, provides the `dreal` 
executable in `PATH` and mounts the `benchmarks/` directory for easy file
transfers.

We outline briefly how to create new ∫dReal inputs and tweak ∫dReal's 
options in `benchmarks/REF.md`.

## Licensing
(The full licence may be seen in `LICENSE` in the top-level directory).

Copyright (C) 2025  Cody Rivera

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
