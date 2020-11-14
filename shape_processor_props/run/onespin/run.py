#!/bin/env python3

import sys

if sys.version_info[0] != 3 or sys.version_info[1] < 5:
    sys.exit("This script requires Python version 3.5")


import argparse
import os
import pathlib
import subprocess


parser = argparse.ArgumentParser()
args = parser.parse_args()

subprocess.check_call(['onespin', '-i', 'init.tcl'],
                      env=dict(os.environ, ROOT=str(pathlib.Path(__file__).resolve().parents[3])))
