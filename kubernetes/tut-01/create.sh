#!/bin/bash

cat tutorial.md  | grep '\$' | sed 's@\$@@g' | sh
