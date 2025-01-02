FROM ubuntu:18.04
LABEL authors="bhusalb"

COPY . /usr/fairsquare
WORKDIR /usr/fairsquare

ENV DEBIAN_FRONTEND=noninteractive

# Update the package list and install required dependencies, including CMake
RUN apt-get update && \
    apt-get install -y python3 python3-pip nano cmake build-essential wget && \
    rm -rf /var/lib/apt/lists/*

# Install CMake 3.16 or higher
RUN wget https://github.com/Kitware/CMake/releases/download/v3.16.9/cmake-3.16.9-Linux-x86_64.sh && \
    chmod +x cmake-3.16.9-Linux-x86_64.sh && \
    ./cmake-3.16.9-Linux-x86_64.sh --skip-license --prefix=/usr/local && \
    rm cmake-3.16.9-Linux-x86_64.sh


# Set Python3 as the default Python
RUN ln -s /usr/bin/python3 /usr/bin/python


RUN pip3 install z3-solver

RUN pip3 install scipy pandas

RUN pip3 install codegen asteval==0.9.10 scikit-learn scipy

RUN pip3 install Pillow==6.1.0 matplotlib==2.2.0

RUN apt-get install python3-tk

RUN apt install gnuplot-qt libxcursor1 libxrandr2

CMD ["/bin/bash"]