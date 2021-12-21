# based on https://github.com/diffblue/cbmc/Dockerfile

FROM ubuntu:20.04 as builder
ENV DEBIAN_FRONTEND noninteractive
ENV DEBCONF_NONINTERACTIVE_SEEN true
# Timezone data is needed during the installation of dependencies,
# since cmake depends on the tzdata package. In an interactive terminal,
# the user selects the timezone at installation time. Since this needs
# to be a non-interactive terminal, we need to setup some sort of default.
# The UTC one seemed the most suitable one.
RUN echo 'tzdata tzdata/Areas select Etc' | debconf-set-selections; \
    echo 'tzdata tzdata/Zones/Etc select UTC' | debconf-set-selections; \
    apt-get update && apt-get upgrade -y && apt-get install --no-install-recommends -y \
    python3 python3-pip \
    cmake \
    make \
    ninja-build \
    gcc \
    g++ \
    maven \
    flex \
    bison \
    libxml2-utils \
    patch \
    libboost-program-options-dev \
    ccache \
    zlib1g-dev wget libgmp-dev unzip libc6-dev gcc-multilib g++-multilib vim emacs nano jq git
COPY . /dsharpy
WORKDIR /dsharpy
RUN rm -fr tools/*/build
RUN ./update.sh

# install dsharpy
RUN pip3 install poetry
RUN poetry install

# build M4RI for ApproxFlow
WORKDIR /
RUN wget https://bitbucket.org/malb/m4ri/downloads/m4ri-20200125.tar.gz
RUN tar -xvf m4ri-20200125.tar.gz
WORKDIR m4ri-20200125
RUN ./configure
RUN make && make install

# build CryptoMiniSat for ApproxFlow
WORKDIR /
RUN wget https://github.com/msoos/cryptominisat/archive/5.8.0.tar.gz
RUN tar -xvf 5.8.0.tar.gz
WORKDIR /cryptominisat-5.8.0
RUN mkdir build
WORKDIR /cryptominisat-5.8.0/build
RUN cmake -DSTATICCOMPILE=ON ..
RUN make -j6 && make install

# build ApproxMC for ApproxFlow
RUN git clone https://github.com/meelgroup/approxmc /approxmc
WORKDIR /approxmc
RUN git checkout c9144b7b0f1c13f5c2f2d507e9493093b1afd4ff
RUN mkdir build
WORKDIR /approxmc/build
RUN cmake -DSTATICCOMPILE=ON ..
RUN make -j6 && make install
RUN cp /approxmc/build/approxmc /dsharpy/tools
WORKDIR /dsharpy
