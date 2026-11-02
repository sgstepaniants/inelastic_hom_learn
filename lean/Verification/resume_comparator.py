#!/usr/bin/env python3
"""Finish missing sandboxed checks, preserving each completed local result."""

import fcntl
import json
from pathlib import Path
import platform
import shutil

from collect_comparator import collect
import verify


PILOT = ("dirichlet_compactness", "dirichlet_weak_compactness", "homogenized_green")


def combine(sources, destination):
    destination.mkdir(parents=True, exist_ok=True)
    for path in destination.glob("comparator-*"):
        if path.is_file():
            path.unlink()
    for source in sources:
        for record in sorted(source.glob("comparator-*.json")):
            target = destination / record.name
            if target.exists():
                raise ValueError(f"Duplicate evidence: {record.name}")
            shutil.copyfile(record, target)
            log = record.with_suffix(".log")
            if log.exists():
                shutil.copyfile(log, target.with_suffix(".log"))
    summary = collect(destination)
    (destination / "coverage.json").write_text(json.dumps(summary, indent=2) + "\n")
    if summary["unexpected"] or summary["duplicates"]:
        raise ValueError("Unexpected or duplicate Comparator results")
    return summary


def main():
    if platform.system() != "Linux":
        raise SystemExit("Run this recovery inside the Linux proof VM.")
    results = verify.ROOT / "Verification/results"
    saved = results / "ci"
    local = results / "local"
    combined = results / "combined"
    local.mkdir(parents=True, exist_ok=True)
    lock_path = verify.ROOT / ".work/local-comparator.lock"
    lock_path.parent.mkdir(exist_ok=True)
    with lock_path.open("w") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise SystemExit("A local Comparator recovery is already running.")
        baseline = collect(saved)
        if baseline["failed_or_invalid"] or baseline["unexpected"] or baseline["duplicates"]:
            raise SystemExit("Preserved CI evidence is invalid; refusing to reuse it.")
        summary = combine([saved, local], combined)
        pending = {
            Path(name).stem.removeprefix("comparator-")
            for name in summary["missing"] + summary["failed_or_invalid"]
        }
        order = [name for name in PILOT if name in pending]
        order += sorted(pending - set(PILOT))
        print(f"Preserving {summary['configurations_received'] - len(summary['failed_or_invalid'])} "
              f"successful checks; {len(order)} remain", flush=True)
        verify.RESULTS = local
        for index, name in enumerate(order, 1):
            print(f"Recovery {index}/{len(order)}: {name}", flush=True)
            failed = False
            try:
                verify.comparator(selected=[name], clear_existing=False)
            except SystemExit:
                failed = True
            finally:
                summary = combine([saved, local], combined)
                valid = summary["configurations_received"] - len(summary["failed_or_invalid"])
                print(f"Validated {valid}/{summary['configurations_expected']} configurations",
                      flush=True)
            if failed and name in PILOT:
                raise SystemExit(f"Repaired pilot failed: {name}; completed evidence preserved.")
        if not summary["passed"]:
            raise SystemExit("Comparator coverage is incomplete; resume after resolving failures.")
        print("All configurations passed sandboxed Comparator and all six kernels.", flush=True)


if __name__ == "__main__":
    main()
