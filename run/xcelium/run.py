#!/bin/env python3

import sys

if sys.version_info[0] != 3 or sys.version_info[1] < 5:
    sys.exit("This script requires Python version 3.5")


import argparse
import os
import pathlib
import subprocess


parser = argparse.ArgumentParser()
parser.add_argument('test', metavar='TEST')
args = parser.parse_args()

cmd = ['xrun']
cmd.append('-q')
cmd.extend(['-uvm', '-uvmhome', 'CDNS-1.2'])
cmd.extend(['-f', 'files.f'])
cmd.append('+UVM_TESTNAME={}'.format(args.test))

subprocess.check_call(cmd,
                      env=dict(os.environ, ROOT=str(pathlib.Path(__file__).resolve().parents[2])))
