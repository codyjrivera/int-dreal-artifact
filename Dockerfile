# Supporting Artifact for
# "Checking 𝛿-Satisfiability of Reals with Integrals"
# by Cody Rivera, Bishnu Bhusal, Rohit Chadha, A. Prasad Sistla,
# and Mahesh Viswanathan.
# 
# Artifact by Cody Rivera and Bishnu Bhusal, 2025. 
#
# Dockerfile for artifact.

FROM ubuntu:22.04
COPY . /home/ubuntu/int-dreal-artifact
WORKDIR /home/ubuntu/int-dreal-artifact
RUN apt-get update
RUN apt install apt-transport-https curl gnupg -y 

# Build ∫dReal
RUN curl -fsSL https://bazel.build/bazel-release.pub.gpg | gpg --dearmor >bazel-archive-keyring.gpg
RUN mv bazel-archive-keyring.gpg /usr/share/keyrings
RUN echo "deb [arch=amd64 signed-by=/usr/share/keyrings/bazel-archive-keyring.gpg] https://storage.googleapis.com/bazel-apt stable jdk1.8" | tee /etc/apt/sources.list.d/bazel.list
RUN apt update

RUN apt install -y --no-install-recommends build-essential
RUN apt-get install -y --no-install-recommends bison coinor-libclp-dev g++ libfl-dev libgmp-dev libnlopt-cxx-dev libpython3-dev pkg-config python3-distutils python3-minimal zlib1g-dev

RUN apt install -y cmake
RUN apt install -y libmpfr-dev 
RUN apt install -y python3-pip
RUN apt install -y  bazel-5.1.0

RUN cd ibex-lib && mkdir build && cd build && cmake -DBUILD_SHARED_LIBS=On .. && (make -j 6 || echo "There were failing tests!")

RUN mkdir -p /usr/local/lib/ibex/3rd

RUN cp /home/ubuntu/int-dreal-artifact/ibex-lib/build/interval_lib_wrapper/gaol/gaol-4.2.0/lib/libgaol-4.2.so.0 /usr/local/lib/ibex/3rd
RUN cp /home/ubuntu/int-dreal-artifact/ibex-lib/build/interval_lib_wrapper/gaol/gaol-4.2.0/lib/libgaol-4.2.so.0 /usr/local/lib/ibex/3rd
RUN cp /home/ubuntu/int-dreal-artifact/ibex-lib/build/interval_lib_wrapper/gaol/gaol-4.2.0/lib/libgaol-4.2.so.0.0.0 /usr/local/lib/ibex/3rd
RUN cp /home/ubuntu/int-dreal-artifact/ibex-lib/build/interval_lib_wrapper/gaol/gaol-4.2.0/lib/libgaol.so /usr/local/lib/ibex/3rd

RUN cp /home/ubuntu/int-dreal-artifact/ibex-lib/build/interval_lib_wrapper/gaol/mathlib-2.1.0/lib/libultim-2.1.so.0 /usr/local/lib/ibex/3rd
RUN cp /home/ubuntu/int-dreal-artifact/ibex-lib/build/interval_lib_wrapper/gaol/mathlib-2.1.0/lib/libultim-2.1.so.0.0.0 /usr/local/lib/ibex/3rd
RUN cp /home/ubuntu/int-dreal-artifact/ibex-lib/build/interval_lib_wrapper/gaol/mathlib-2.1.0/lib/libultim.so /usr/local/lib/ibex/3rd

RUN cd /home/ubuntu/int-dreal-artifact/ibex-lib/build && make -j 6 && make install

RUN cp /home/ubuntu/int-dreal-artifact/ibex-lib/build/flint/flint-2.9.0/lib/libflint.so /usr/local/lib/
RUN cp /home/ubuntu/int-dreal-artifact/ibex-lib/build/arb/arb-2.23.0/lib/libarb.so /usr/local/lib/
RUN cp /home/ubuntu/int-dreal-artifact/ibex-lib/build/interval_lib_wrapper/gaol/gaol-4.2.0/lib/libgdtoa.so /usr/local/lib/
RUN cp /home/ubuntu/int-dreal-artifact/ibex-lib/build/interval_lib_wrapper/gaol/gaol-4.2.0/lib/libgdtoa.so.0 /usr/local/lib/
RUN cp /home/ubuntu/int-dreal-artifact/ibex-lib/build/flint/flint-2.9.0/lib/libflint.so.17 /usr/local/lib/
RUN cp /home/ubuntu/int-dreal-artifact/ibex-lib/build/arb/arb-2.23.0/lib/libarb.so.2 /usr/local/lib/
RUN export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib/ibex/3rd/
RUN export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib/

RUN cd /home/ubuntu/int-dreal-artifact/dreal4 && bazel-5.1.0 build //...

RUN cd /home/ubuntu/int-dreal-artifact/dreal-integral-experiments/ && pip3 install -r requirements.txt

ENV PATH="$PATH:/home/ubuntu/int-dreal-artifact/dreal4/bazel-bin/dreal/"
# End build ∫dReal

# Set up FairSquare
ENV DEBIAN_FRONTEND=noninteractive

# Update the package list and install required dependencies, including CMake
RUN apt-get update && \
    apt-get install -y python3-pip nano cmake build-essential wget && \
    rm -rf /var/lib/apt/lists/*

# Set Python3 as the default Python
RUN ln -s /usr/bin/python3 /usr/bin/python

RUN pip3 install z3-solver

RUN pip3 install scipy pandas

RUN pip3 install codegen asteval==0.9.10 scikit-learn scipy

RUN pip3 install Pillow==6.1.0 matplotlib==2.2.0

RUN apt-get install python3-tk

RUN apt install gnuplot-qt libxcursor1 libxrandr2
# End set up FairSquare

CMD ["/bin/bash"]