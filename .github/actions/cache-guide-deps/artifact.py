"""Recover the four Guide dependency builds from a successful scheduled docs run on main."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile

from key import PATHS


def api(endpoint):
    return json.loads(subprocess.check_output(["gh", "api", endpoint], timeout=30))


def producer(repository, key):
    prefix = f"repos/{repository}/actions"
    artifacts = api(f"{prefix}/artifacts?name={key}&per_page=100")["artifacts"]
    candidates = {a["workflow_run"]["id"] for a in artifacts
                  if a["name"] == key and not a["expired"] and a.get("workflow_run")}
    if not candidates:
        return None
    runs = api(f"{prefix}/workflows/docs.yml/runs?branch=main&event=schedule"
               "&status=success&per_page=14")["workflow_runs"]
    return next((r["id"] for r in runs if r["id"] in candidates
                 and r["event"] == "schedule" and r["head_branch"] == "main"
                 and r["conclusion"] == "success" and r["path"] == ".github/workflows/docs.yml"
                 and (r.get("head_repository") or {}).get("full_name") == repository), None)


def pack(root, archive):
    def regular_output(member):
        if (root / member.name).is_symlink() or not (member.isfile() or member.isdir()):
            raise ValueError(f"Unexpected Guide build output: {member.name!r}")
        return member

    with tarfile.open(archive, "w:gz", compresslevel=1, dereference=True) as tar:
        for path in PATHS:
            tar.add(root / path, arcname=path, filter=regular_output)


def install(root, archive):
    # Stage on the destination filesystem. A failed extraction leaves no partial build for Lake.
    with tempfile.TemporaryDirectory(dir=root / ".lake") as tmp:
        staging = Path(tmp)
        with tarfile.open(archive, "r:gz") as tar:
            for member in tar:
                path = Path(member.name)
                if (not any(path.is_relative_to(p) for p in PATHS) or ".." in path.parts
                        or not (member.isfile() or member.isdir())):
                    raise ValueError(f"Unexpected Guide archive member: {member.name!r}")
                tar.extract(member, staging, filter="data")
        if not all((staging / p).is_dir() and not (root / p).exists() for p in PATHS):
            raise ValueError("Missing Guide build or destination already exists")
        installed = []
        try:
            for path in PATHS:
                destination = root / path
                destination.parent.mkdir(parents=True, exist_ok=True)
                (staging / path).rename(destination)
                installed.append(destination)
        except OSError:
            for destination in installed:
                shutil.rmtree(destination)
            raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("pack").add_argument("archive", type=Path)
    commands.add_parser("restore").add_argument("key")
    args = parser.parse_args()
    if args.command == "pack":
        pack(Path.cwd(), args.archive)
        return
    repo = os.environ["GITHUB_REPOSITORY"]
    run = producer(repo, args.key)
    if not run:
        print("No compatible scheduled Guide artifact. Lake will build the dependencies.")
        return
    with tempfile.TemporaryDirectory() as tmp:
        subprocess.run(["gh", "run", "download", str(run), "--repo", repo,
                        "--name", args.key, "--dir", tmp], check=True, timeout=120)
        install(Path.cwd(), Path(tmp) / "guide-builds.tar.gz")
    print(f"Restored Guide dependency builds from docs run {run}.")


if __name__ == "__main__":
    main()
