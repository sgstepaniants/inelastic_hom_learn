#!/usr/bin/env python3
"""Build the proof library, check its axioms, or run sandboxed Comparator."""

import argparse
import json
from pathlib import Path
import platform
import re
import shlex
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "Verification" / "results"
STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}


def run(command, name):
    RESULTS.mkdir(exist_ok=True)
    (RESULTS / f"{name}.json").unlink(missing_ok=True)
    log = RESULTS / f"{name}.log"
    print("Running " + shlex.join(command), flush=True)
    started = time.monotonic()
    with log.open("w") as output:
        result = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
    record = {
        "command": command,
        "exit_code": result.returncode,
        "seconds": round(time.monotonic() - started, 1),
    }
    return record, log


def save(name, record):
    (RESULTS / f"{name}.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record), flush=True)


def configurations():
    files = sorted((ROOT / "Comparator").glob("*.json"))
    if not files:
        raise SystemExit("No Comparator configurations found")
    names = []
    for path in files:
        config = json.loads(path.read_text())
        if not config["theorem_names"]:
            raise SystemExit(f"No theorem selections in {path.name}")
        if not set(config["permitted_axioms"]) <= STANDARD_AXIOMS:
            raise SystemExit(f"Unexpected permitted axiom in {path.name}")
        if config.get("definition_names"):
            raise SystemExit(f"Definition holes in {path.name}")
        names.extend(config["theorem_names"])
    if len(names) != len(set(names)):
        raise SystemExit("Duplicate Comparator theorem selection")
    return files, set(names)


def build():
    record, _ = run([
        "lake", "build", "KVApproximation", "Challenges", "TauCeti",
        "ForTauCeti", "NeuralNetworkProofs",
    ], "build")
    record["passed"] = record["exit_code"] == 0
    save("build", record)
    if not record["passed"]:
        raise SystemExit(1)


def axioms():
    _, selected = configurations()
    source = ROOT / "Verification" / "Axioms.lean"
    queries = re.findall(r"^#print axioms\s+(\S+)", source.read_text(), re.M)
    if len(queries) != len(set(queries)) or not selected <= set(queries):
        raise SystemExit("Axiom audit must include every Comparator selection exactly once")
    record, log = run([
        "lake", "env", "lean", "-j1", "-M4096", "--root=.", "Verification/Axioms.lean",
    ], "axioms")
    output = log.read_text()
    results = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.M)
    empty = re.findall(r"^'([^']+)' does not depend on any axioms", output, re.M)
    names = [name for name, _ in results] + empty
    found = {a.strip() for _, values in results for a in values.split(",") if a.strip()}
    exact = len(names) == len(set(names)) == len(queries) and set(names) == set(queries)
    record.update(declarations=len(queries), results=len(names), coverage_matches=exact,
                  axioms=sorted(found))
    record["passed"] = record["exit_code"] == 0 and exact and found <= STANDARD_AXIOMS
    save("axioms", record)
    if not record["passed"]:
        raise SystemExit(1)


def comparator():
    if platform.system() != "Linux":
        raise SystemExit("Sandboxed Comparator requires Linux with bubblewrap.")
    RESULTS.mkdir(exist_ok=True)
    for path in RESULTS.glob("comparator-*"):
        if path.suffix in {".json", ".log"}:
            path.unlink()
    files, _ = configurations()
    for path in files:
        name = "comparator-" + path.stem
        record, _ = run([
            "lake", "comparator", "--config=" + str(path.relative_to(ROOT)), "--paranoid",
        ], name)
        record["passed"] = record["exit_code"] == 0
        save(name, record)
        if not record["passed"]:
            raise SystemExit(1)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", choices=["build", "axioms", "local", "comparator"],
                        nargs="?", default="local")
    stage = parser.parse_args().stage
    if stage in {"build", "local"}:
        build()
    if stage in {"axioms", "local"}:
        axioms()
    if stage == "comparator":
        comparator()
