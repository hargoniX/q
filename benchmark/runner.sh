#!/bin/bash
stdbuf --output=L python -u benchmark/runner.py -f benchmark/config.toml -d 3 | tee benchmark/log.txt
