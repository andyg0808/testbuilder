#!/bin/zsh
cd $(dirname $0)
file=../research/anon-p2-submissions/uncommented/115/linked_list.py
# export PYTHONOPTIMIZE=1 profile=1 time=1
export PYTHONOPTIMIZE=1 time=1
#export filter="lambda x: x <= 85"
pipenv run python3 profiling_run.py $file
