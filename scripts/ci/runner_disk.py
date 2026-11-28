"""Sample available space through a hosted Lean job to calibrate its SDK cleanup threshold."""

import os
from pathlib import Path
import shutil
import subprocess
import sys
import time


def free_bytes():
    return shutil.disk_usage("/").free


def record(directory):
    free = free_bytes()
    low = directory / "minimum"
    if free < int(low.read_text()):
        pending = directory / "minimum.tmp"
        pending.write_text(str(free))
        pending.replace(low)


def main():
    directory = Path(os.environ["RUNNER_TEMP"]) / "lean-disk-sample"
    mode = sys.argv[1]
    if mode == "start":
        directory.mkdir()
        initial = str(free_bytes())
        for name in ("initial", "minimum"):
            (directory / name).write_text(initial)
        subprocess.Popen([sys.executable, __file__, "sample"], stdin=subprocess.DEVNULL,
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                         start_new_session=True)
    elif mode == "sample":
        while not (directory / "stop").exists():
            record(directory)
            time.sleep(5)
    elif mode == "report":
        (directory / "stop").touch()
        initial = int((directory / "initial").read_text())
        minimum = min(free_bytes(), int((directory / "minimum").read_text()))
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as summary:
            print(f"Lean runner disk after setup: {initial / 2**30:.1f} GiB free. "
                  f"Minimum sampled free space: {minimum / 2**30:.1f} GiB. "
                  f"Largest sampled decrease: {(initial - minimum) / 2**30:.1f} GiB "
                  "(five-second samples).", file=summary)
    else:
        raise ValueError(f"Unknown measurement mode: {mode}")


if __name__ == "__main__":
    main()
