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
parser.add_argument('-g', '--gui', action='store_true')
parser.add_argument('--coverage', action='store_true')
parser.add_argument('--tool-args')
args = parser.parse_args()

cmd = ['xrun']
cmd.extend(['-errormax', '1'])
cmd.append('-q')
cmd.extend(['-uvm', '-uvmhome', 'CDNS-1.2'])
cmd.extend(['-f', 'files.f'])
cmd.append('+UVM_TESTNAME={}'.format(args.test))

if args.gui:
    cmd.extend(['-gui', '-access', 'rwc'])

if args.coverage:
    cmd.extend(['-coverage', 'functional'])
    cmd.append('-covoverwrite')

if args.tool_args:
    cmd.extend(args.tool_args.split())


subprocess.check_call(cmd,
                      env=dict(os.environ, ROOT=str(pathlib.Path(__file__).resolve().parents[2])))
