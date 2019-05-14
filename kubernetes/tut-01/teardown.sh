#!/bin/bash

for a in `(ls *.yaml)`; do kubectl delete -f $a; done
