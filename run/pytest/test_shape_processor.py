import itertools
import pathlib
import subprocess

import pytest


ROOT = pathlib.Path(__file__).resolve().parents[2]


@pytest.fixture(autouse=True, scope='module')
def build(tmpdir_factory):
    print('Building')
    build_dir = tmpdir_factory.mktemp('build')
    with build_dir.as_cwd():
        subprocess.check_call([
                str(ROOT.joinpath('run/xcelium/run.py')),
                '--coverage',
                '--tool-args=-elaborate',
                'dummy',
                ])
    return build_dir


@pytest.fixture(scope='module')
def merge():
    dirs = []
    yield dirs
    print('Merging')
    runs = ' '.join(str(dir) for dir in dirs)
    subprocess.check_call([
            'imc',
            '-execcmd', 'merge -overwrite -out merged {}'.format(runs)])


tests = [('random_ctrl_writes', 5)]


def to_params(tests):
    result = []
    for test in tests:
        if isinstance(test, str):
            result.append((test, 0))
        else:
            result.extend(itertools.product([test[0]], range(test[1])))
    return result


@pytest.mark.parametrize('test, exec_number', to_params(tests))
def test_run(build, tmpdir, test, exec_number, merge):
    print('Running', test)
    with tmpdir.as_cwd():
        subprocess.check_call([
                str(ROOT.joinpath('run/xcelium/run.py')),
                '--tool-args=-R -xmlibdirpath {}'.format(build),
                test,
                ])
    merge.append(tmpdir.join('cov_work/scope/test'))
