#!/usr/bin/bash

xhost +

CURDIR=`(pwd)`
fc_source=$CURDIR/freecad-source
fc_build=$CURDIR/freecad-bin
other_files=$CURDIR/freecad-other

docker run -it --rm \
    -v $fc_source:/mnt/source \
    -v $fc_build:/mnt/build \
    -v $other_files:/mnt/files \
    -e "DISPLAY" -e "QT_X11_NO_MITSHM=1" -v /tmp/.X11-unix:/tmp/.X11-unix:ro \
    freecad-container:latest

