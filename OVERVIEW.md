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

Although the primary experimental laptop has 32 GB of RAM, our benchmarks
will run in under XX GB.

## Getting Started
We start by providing users with a Docker container incorporating ∫dReal,
XX FairSquare XX, and our benchmark suite. There are two ways of running
this container: use our prebuilt Docker image, or build a new Docker image.

### Use an Existing Docker Image
The provided image - `int-dreal-image` supplies an Ubuntu 22.04 environment 
and the software to run the benchmarks. Here are the directions to use
this image:
1. Install Docker Engine. See [here](https://docs.docker.com/engine/install/) for
   instructions. Another requirement is `unzip`.
2. Run `unzip ids-docker.zip` to extract the image, `ids-artifact.tar`.
3. Run `docker load ids-artifact.tar` to load the extracted image into Docker.
3. To obtain an interactive shell for the container `ids-artifact`, run 
   `docker run -it --mount type=bind,src="$(pwd)",target=/outpwd ids-artifact /bin/bash`.
   (the `--mount` option allows you to copy files to the host machine).

### Build a New Docker Image
Below are instructions for building a new Docker image.
1. Install Docker Engine. See [here](https://docs.docker.com/engine/install/) for
   instructions.
2. In the root directory of this artifact, run `docker build -t ids-artifact .` to
   build the container.
3. To obtain an interactive shell for the container `ids-artifact`, run 
   `docker run -it --mount type=bind,src="$(pwd)",target=/outpwd ids-artifact /bin/bash`.
   (the `--mount` option allows you to copy files to the host machine).