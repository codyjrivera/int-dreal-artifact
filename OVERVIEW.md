# Supporting Artifact for "Checking 𝛿-Satisfiability of Reals with Integrals"
by Cody Rivera, Bishnu Bhusal, Rohit Chadha, A. Prasad Sistla,
and Mahesh Viswanathan.

Artifact by Cody Rivera and Bishnu Bhusal, Version 1.0, 2025.

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

## Step by Step Instructions
We detail how one can use our artifact to show our paper's claims in this
section.

### Support for Claim 1 (can add integration to 𝛿-decision procedures)

### Support for Claim 2 (can use ∫dReal in verification and synthesis)

### Support for Claim 3 (performance evaluation of ∫dReal and other tools)

#### Claim 3, Part 1 (running ∫dReal on benchmarks)

#### Claim 3, Part 2 (running Mathematica on benchmarks)
Since Wolfram Mathematica is proprietary software, we do not include it in
a Docker image. However, we do provide equivalent benchmarks and a
script that can be used to run them. 

#### Claim 3, Part 3 (generating Table 3)

#### Claim 3, Part 4 (running FairSquare on benchmarks)
For a subset of our benchmarks related to algorithmic fairness, including
`high_inc_gd_00`, `high_inc_gd_unfair_00`, `eth_colrank_fair_00`, and
`eth_colrank_unfair_00`, we evaluate the fairness of the program from which
we obtain our queries using FairSquare. The benchmarks can be seen in the 
directory `fairsquare/dreal`. We provide a separate Docker image for running
FairSquare benchmarks. To run these benchmarks, perform the following steps 
(starting from the top-level directory and outside of a container):

1. Run `cd fairsquare`.
2. Run `docker load -i fairsquare-image.tar` to load the FairSquare image.
3. Run `docker run -it fairsquare-image /bin/bash` to enter an interactive
   shell.
4. Run `cd src`.
5. Run `python3 benchmark.py` to run FairSquare on the appropriate
   benchmarks.
6. Run `cat result.csv` to output the results.

The results corresponding to Table 3 should be in the file `result.csv`. An
example `result.csv` can be seen in the file `fairsquare/example-result.csv`
(relative to the top-level directory of the *artifact*).

### Use an Existing Docker Image
The provided image `fairsquare-image.tar` supplies an Ubuntu 18.04 environment 
and the software to run the benchmarks. Here are the directions to use
this image:
1. Install Docker Engine. See [here](https://docs.docker.com/engine/install/)
   for instructions.
2. Run `docker load fairsquare-image.tar` to load the extracted image into
   Docker.
3. To obtain an interactive shell for the container `fairsquare-image`, run
   the following command:
```
docker run -it fairsquare-image /bin/bash
```
   (the `--mount` option allows you to copy files to the host machine).


### Support for Claim 4 (scalability evaluation of ∫dReal)


## Reusability Guide
The reusability of our artifact comprises the ability to write new queries
in the SMT-LIB based input language of ∫dReal, and evaluate them. Our Docker
image, if used according to our instructions, provides the `dreal` 
executable in `PATH` and mounts the `benchmarks/` directory for easy file
transfers.

We describe briefly how to create new ∫dReal inputs and tweak ∫dReal's 
options in `benchmarks/REUSE.md`.
