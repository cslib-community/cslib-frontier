"""Recover the four Guide dependency builds from a successful scheduled docs run on main."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
import zipfile

from key import PATHS


def api(endpoint):
    return json.loads(subprocess.check_output(["gh", "api", endpoint], timeout=30))


def producer(repository, key):
    prefix = f"repos/{repository}/actions"
    runs = api(f"{prefix}/workflows/docs.yml/runs?branch=main&event=schedule"
               "&status=success&per_page=14")["workflow_runs"]
    for run in runs:
        if (run["event"] != "schedule" or run["head_branch"] != "main"
                or run["conclusion"] != "success" or run["path"] != ".github/workflows/docs.yml"
                or (run.get("head_repository") or {}).get("full_name") != repository):
            continue
        # A successful rerun may fail its optional backup step. Never relabel an earlier
        # attempt's artifact with the successful attempt number returned by the runs API.
        name = f"{key}-run-{run['id']}-attempt-{run['run_attempt']}"
        artifacts = api(f"{prefix}/runs/{run['id']}/artifacts?name={name}&per_page=100")["artifacts"]
        for artifact in artifacts:
            if (artifact["name"] == name and not artifact["expired"]
                    and (artifact.get("workflow_run") or {}).get("id") == run["id"]):
                return run["id"], run["run_attempt"], artifact["id"]
    return None


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
    selected = producer(repo, args.key)
    if not selected:
        print("No compatible scheduled Guide artifact. Lake will build the dependencies.")
        return
    run, attempt, artifact_id = selected
    with tempfile.TemporaryDirectory() as tmp:
        package = Path(tmp) / "artifact.zip"
        with package.open("wb") as stream:
            subprocess.run(["gh", "api", f"repos/{repo}/actions/artifacts/{artifact_id}/zip"],
                           stdout=stream, check=True, timeout=120)
        current = api(f"repos/{repo}/actions/runs/{run}")
        if current["run_attempt"] != attempt or current["conclusion"] != "success":
            raise ValueError("Guide producer was rerun during download")
        archive = Path(tmp) / "guide-builds.tar.gz"
        with zipfile.ZipFile(package) as bundle:
            if bundle.namelist() != [archive.name]:
                raise ValueError("Unexpected Guide artifact contents")
            with bundle.open(archive.name) as source, archive.open("wb") as destination:
                shutil.copyfileobj(source, destination)
        install(Path.cwd(), archive)
    print(f"Restored Guide dependency builds from docs run {run} attempt {attempt}, artifact {artifact_id}.")



if __name__ == "__main__":
    main()
