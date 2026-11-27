"""Select expensive CI jobs from the complete diff of the checked-out event revision."""

import json
import os
from pathlib import Path
import re
import subprocess


def prose_path(path: str) -> bool:
    """Markdown maintained as prose, outside the compiled registries and Guide."""
    return (path in {"AGENTS.md", "README.md", "CONTRIBUTING.md", "ROADMAP.md"}
            or re.fullmatch(r"(policy|roadmap|results)/[^/]+\.md", path) is not None)


def classify(event: str, paths: list[str]) -> tuple[bool, bool]:
    """Return whether to run Lean and the origin suite. Unknown changes get both."""
    if not paths or event not in {"pull_request", "merge_group"}:
        return True, True
    docs_only = all(prose_path(path) for path in paths)
    origin_unaffected = all(
        prose_path(path) or path == "references.bib"
        or re.fullmatch(r"CslibFrontier(?:Tests|Results)?(?:/[^/]+)*\.lean", path)
        for path in paths)
    return event != "pull_request" or not docs_only, not origin_unaffected


def git(*args: str) -> bytes:
    return subprocess.check_output(["git", *args])


def event_paths(event: str, payload: dict, sha: str) -> list[str]:
    if git("rev-parse", "HEAD").decode().strip() != sha:
        raise ValueError("checkout differs from event SHA")
    if event == "pull_request":
        parents = git("show", "-s", "--format=%P", sha).decode().split()
        if len(parents) != 2 or parents[1] != payload["pull_request"]["head"]["sha"]:
            raise ValueError("pull request merge parents do not match the event")
        base = parents[0]
    else:
        group = payload["merge_group"]
        base = group["base_sha"]
        if group["head_sha"] != sha or not re.fullmatch("[0-9a-f]{40}", base):
            raise ValueError("invalid merge group range")
        if subprocess.run(["git", "cat-file", "-e", f"{base}^{{commit}}"],
                          stderr=subprocess.DEVNULL).returncode:
            git("fetch", "--no-tags", "--depth=1", "origin", base)
    diff = git("diff", "--no-renames", "--name-only", "-z", base, sha, "--")
    return [os.fsdecode(path) for path in diff.split(b"\0") if path]


def main() -> None:
    event = os.environ["GITHUB_EVENT_NAME"]
    paths = []
    if event in {"pull_request", "merge_group"} and os.getenv("FORCE_FULL_CI") not in {"1", "true"}:
        try:
            payload = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_bytes())
            paths = event_paths(event, payload, os.environ["GITHUB_SHA"])
        except (KeyError, ValueError, OSError, subprocess.CalledProcessError) as error:
            print(f"Full validation because the comparison is unavailable: {error}")
    lean, origin = classify(event, paths)
    print(f"{len(paths)} changed paths; Lean: {lean}; HTTP cache origin: {origin}")
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        print(f"lean={str(lean).lower()}\norigin={str(origin).lower()}", file=output)


if __name__ == "__main__":
    main()
