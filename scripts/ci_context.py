#!/usr/bin/env python3
"""Reject stale PR heads and bases using trusted, read-only GitHub context.

Every candidate uses the same complete Lean gate. Labels, comments and candidate
configuration cannot authorize an exemption from mathematical verification.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import sys
import urllib.request

SHA = re.compile(r"[0-9a-f]{40}")
REPOSITORY = re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+")


def api_json(path: str) -> tuple[object, str | None]:
    headers = {"Accept": "application/vnd.github+json", "User-Agent": "SubGaussianTailBounds-CI"}
    token = os.environ.get("GH_TOKEN", "")
    if token:
        headers["Authorization"] = f"Bearer {token}"
    request = urllib.request.Request("https://api.github.com" + path, headers=headers)
    with urllib.request.urlopen(request, timeout=30) as response:
        return json.load(response), response.headers.get("Link")


def resolve(event: dict, fetch=api_json) -> dict:
    if "pull_request" not in event:
        return {"base_ref": "", "head_sha": ""}
    pr = event["pull_request"]
    repository = event["repository"]["full_name"]
    number = event["number"]
    head, base = pr["head"]["sha"], pr["base"]["sha"]
    if not REPOSITORY.fullmatch(repository) or not isinstance(number, int) or number < 1:
        raise ValueError("Invalid GitHub repository or PR number.")
    if not SHA.fullmatch(head) or not SHA.fullmatch(base):
        raise ValueError("Invalid GitHub commit SHA.")
    live, _ = fetch(f"/repos/{repository}/pulls/{number}")
    if live["head"]["sha"] != head:
        raise ValueError("This CI event is stale; run CI for the latest PR commit.")
    if live["base"]["sha"] != base:
        raise ValueError("The target branch advanced; rerun against the current accepted base revision.")
    return {"base_ref": base, "head_sha": head}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--event", type=Path, required=True)
    args = parser.parse_args()
    context = resolve(json.loads(args.event.read_text()))
    output = os.environ.get("GITHUB_OUTPUT")
    if output:
        with open(output, "a") as stream:
            stream.write(f"base_ref={context['base_ref']}\n")
    print(json.dumps(context, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"CI context failed: {error}", file=sys.stderr)
        raise SystemExit(1)
