# roughly based on https://github.com/diffblue/cbmc/Dockerfile

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
    apt-get update && apt-get upgrade -y && apt-get install --no-install-recommends -y ca-certificates \
    bison ccache cmake curl flex g++ g++-multilib gcc gcc-multilib git jq libboost-program-options-dev \
    libc6-dev libgmp-dev libxml2-utils make ninja-build patch unzip wget zlib1g-dev python3 python3-pip
COPY . /dsharpy
WORKDIR /dsharpy
RUN rm -fr tools/*/build
#RUN ./tools/install_approxmc
RUN ./update.sh

# install dsharpy
RUN pip3 install poetry
RUN poetry install

WORKDIR /dsharpy
