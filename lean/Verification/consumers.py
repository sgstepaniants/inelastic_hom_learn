#!/usr/bin/env python3
"""Compile isolated consumers of each subject's exact local dependency closure."""

import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / ".lake" / "build" / "lib" / "lean"
WORK = ROOT / ".work" / "consumers"
RESULTS = ROOT / "Verification" / "results"
LOCAL_PREFIXES = ("KVApproximation.", "TauCeti.", "ForTauCeti.", "NeuralNetworkProofs.")


def imports(source):
    # Read the module header, including nested comments, up to its first declaration.
    position = 0
    result = []
    while position < len(source):
        if source[position].isspace():
            position += 1
        elif source.startswith("--", position):
            end = source.find("\n", position)
            position = len(source) if end == -1 else end + 1
        elif source.startswith("/-", position):
            depth = 1
            position += 2
            while depth and position < len(source):
                if source.startswith("/-", position):
                    depth += 1
                    position += 2
                elif source.startswith("-/", position):
                    depth -= 1
                    position += 2
                else:
                    position += 1
            if depth:
                raise ValueError("Unbalanced module-header comment")
        else:
            end = source.find("\n", position)
            line = source[position:] if end == -1 else source[position:end]
            position = len(source) if end == -1 else end + 1
            if line.strip() in {"module", "prelude"}:
                continue
            match = re.fullmatch(r"(?:(?:public|private|meta)\s+)*import\s+([\w.]+)\s*", line)
            if not match:
                break
            result.append(match[1])
    return result


def main():
    RESULTS.mkdir(exist_ok=True)
    summary = RESULTS / "consumers.json"
    summary.unlink(missing_ok=True)
    modules = {}
    for base in (ROOT / "KVApproximation", ROOT / "Vendor"):
        for path in base.rglob("*.lean"):
            relative = path.relative_to(ROOT if base.name == "KVApproximation" else base)
            modules[".".join(relative.with_suffix("").parts)] = path
    dependencies = {name: imports(path.read_text()) for name, path in modules.items()}
    environment = subprocess.run([
        "lake", "env", "python3", "-c",
        "import json,os; print(json.dumps(os.environ.get('LEAN_PATH','').split(os.pathsep)))",
    ], cwd=ROOT, check=True, capture_output=True, text=True)
    paths = [(ROOT / p).resolve() for p in json.loads(environment.stdout) if p]
    external = [p for p in paths if p != BUILD and not p.is_relative_to(ROOT / ".work")]
    for path in external:
        if any((path / prefix.rstrip(".")).exists() for prefix in LOCAL_PREFIXES):
            raise SystemExit(f"External import path exposes local proof modules: {path}")
    subjects = sorted(p.name for p in (ROOT / "KVApproximation").iterdir() if p.is_dir())
    if not subjects:
        raise SystemExit("No mathematical subjects found")
    records = []
    with (RESULTS / "consumers.log").open("w") as log:
        for subject in subjects:
            selected = sorted(m for m in modules if m.startswith(f"KVApproximation.{subject}."))
            closure = set()

            def visit(name):
                if name in closure:
                    return
                if name not in modules:
                    if name.startswith(LOCAL_PREFIXES):
                        raise ValueError(f"Missing local source: {name}")
                    return
                closure.add(name)
                for dependency in dependencies[name]:
                    visit(dependency)

            for name in selected:
                visit(name)
            target = WORK / subject
            if target.exists():
                shutil.rmtree(target)
            library = target / "lib"
            library.mkdir(parents=True)
            for name in sorted(closure):
                source = modules[name]
                destination = target / source.relative_to(ROOT)
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source, destination)
                relative = Path(*name.split("."))
                for suffix in (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig"):
                    artifact = BUILD / relative.with_suffix(suffix)
                    if suffix == ".olean" and not artifact.is_file():
                        raise ValueError(f"Missing compiled module: {name}; run the full build first")
                    if artifact.is_file():
                        link = library / relative.with_suffix(suffix)
                        link.parent.mkdir(parents=True, exist_ok=True)
                        link.symlink_to(artifact)
            shutil.copy2(ROOT / "LICENSE", target / "LICENSE")
            shutil.copy2(ROOT / "lean-toolchain", target / "lean-toolchain")
            if any(not name.startswith("KVApproximation.") for name in closure):
                (target / "Vendor").mkdir(exist_ok=True)
                shutil.copy2(ROOT / "Vendor" / "NOTICE.md", target / "Vendor" / "NOTICE.md")
            consumer = target / "Consumer.lean"
            consumer.write_text("".join(f"import {name}\n" for name in selected))
            env = os.environ.copy()
            env["LEAN_PATH"] = os.pathsep.join(map(str, [library, *external]))
            command = ["lean", "-j1", "-M4096", "--root=" + str(target), str(consumer)]
            log.write(f"{subject}: {len(selected)} imports, {len(closure)} local modules\n")
            log.flush()
            started = time.monotonic()
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
            record = {
                "subject": subject, "command": command, "imports": len(selected),
                "local_modules": len(closure), "exit_code": result.returncode,
                "seconds": round(time.monotonic() - started, 1), "passed": result.returncode == 0,
            }
            records.append(record)
            print(json.dumps(record), flush=True)
            summary.write_text(json.dumps({
                "method": "isolated imports using copied source closures and production artifacts",
                "external_import_paths": list(map(str, external)),
                "consumers": records,
                "passed": len(records) == len(subjects) and all(r["passed"] for r in records),
            }, indent=2) + "\n")
            if result.returncode:
                raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
