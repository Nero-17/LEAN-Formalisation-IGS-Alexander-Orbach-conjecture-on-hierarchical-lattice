"""Limit heavyweight Lean compilers to two while proof work stays parallel."""
from pathlib import Path
from contextlib import contextmanager
import os
import time
import subprocess
import sys

@contextmanager
def compiler_slot():
    if sys.platform != 'win32':
        yield
        return
    import msvcrt
    directory = Path(__file__).resolve().parents[1] / 'verification' / 'compiler-slots'
    directory.mkdir(parents=True, exist_ok=True)
    handle = None
    while handle is None:
        for index in range(2):
            candidate = (directory / f'{index}.lock').open('a+b')
            candidate.seek(0, os.SEEK_END)
            if candidate.tell() == 0:
                candidate.write(b'0')
                candidate.flush()
            candidate.seek(0)
            try:
                msvcrt.locking(candidate.fileno(), msvcrt.LK_NBLCK, 1)
                handle = candidate
                break
            except OSError:
                candidate.close()
        if handle is None:
            time.sleep(0.2)
    try:
        yield
    finally:
        handle.seek(0)
        msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
        handle.close()
        # Give already waiting workers a chance before a compiler loop reacquires.
        time.sleep(0.3)

if __name__ == '__main__':
    environment = os.environ.copy()
    environment['ELAN_HOME'] = str(Path.home() / '.elan')
    environment.update(GIT_CONFIG_COUNT='1', GIT_CONFIG_KEY_0='safe.directory', GIT_CONFIG_VALUE_0='*')
    lake = str(Path.home() / '.elan/bin/lake.exe')
    with compiler_slot():
        child = subprocess.Popen([lake, 'env', 'lean', *sys.argv[1:]], env=environment)
        print(f'COMPILER_LAUNCH_PID={child.pid} module={sys.argv[-1]}', flush=True)
        sys.exit(child.wait())
