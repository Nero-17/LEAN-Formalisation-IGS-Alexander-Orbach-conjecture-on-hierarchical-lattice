"""This independent round never updates a previous round archive."""
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).with_name("build_round_archive.py")), run_name="__main__")
