# my freecad dockerfile to build and run the latest freecad version

# install from latest ubuntu
FROM ubuntu:latest AS base_0

# configure a local proxy
# local proxy started with : $ docker run --name apt-cacher-ng -d --restart=always --publish 3142:3142 --volume /srv/docker/apt-cacher-ng:/var/cache/apt-cacher-ng sameersbn/apt-cacher-ng:latest
#RUN echo 'Acquire::http::Proxy "http://http://172.17.0.1:3142";' >> /etc/apt/apt.conf.d/00aptproxy

# update and upgrade libs
RUN apt-get update && \
    apt-get upgrade

# install tz_data
FROM base_0 as base_1

ENV DEBIAN_FRONTEND noninteractive
ENV DEBCONF_NONINTERACTIVE_SEEN=true

## preesed tzdata, update package index, upgrade packages and install needed software
RUN truncate -s0 /tmp/preseed.cfg && \
   (echo "tzdata tzdata/Areas select America" >> /tmp/preseed.cfg) && \
   (echo "tzdata tzdata/Zones/America select Los_Angeles" >> /tmp/preseed.cfg) && \
   debconf-set-selections /tmp/preseed.cfg && \
   rm -f /etc/timezone /etc/localtime && \
   apt-get install -y tzdata
## cleanup of files from setup
RUN rm -rf /tmp/*

# install freecad deps
FROM base_1 as base_2

RUN apt-get install -y cmake cmake-gui libboost-date-time-dev libboost-dev libboost-filesystem-dev libboost-graph-dev libboost-iostreams-dev libboost-program-options-dev libboost-python-dev libboost-regex-dev libboost-serialization-dev libboost-thread-dev libcoin-dev libeigen3-dev libgts-bin libgts-dev libkdtree++-dev libmedc-dev libocct-data-exchange-dev libocct-ocaf-dev libocct-visualization-dev libopencv-dev libproj-dev libpyside2-dev libqt5opengl5-dev libqt5svg5-dev libqt5webkit5-dev libqt5x11extras5-dev libqt5xmlpatterns5-dev libshiboken2-dev libspnav-dev libvtk7-dev libx11-dev libxerces-c-dev libzipios++-dev occt-draw pyside2-tools python3-dev python3-matplotlib python3-pivy python3-ply python3-pyside2.qtcore python3-pyside2.qtgui python3-pyside2.qtsvg python3-pyside2.qtwidgets python3-pyside2.qtnetwork python3-markdown python3-git qtbase5-dev qttools5-dev swig pyqt5-dev-tools
