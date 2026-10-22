#!/usr/bin/env python3
"""Resolve PR context and commit-specific maintenance authorization.

In Actions this script and maintainers.json MUST come from the trusted base
checkout. Contributor-controlled labels, PR text, and head configuration are
never authorization. This script only reads public GitHub metadata.
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


def maintenance_comment(comments: list[dict], maintainers: set[str], head: str) -> bool:
    command = f"/ci-maintenance {head}"
    return any(
        comment.get("body", "").strip() == command
        and comment.get("user", {}).get("login", "").casefold() in maintainers
        and comment.get("user", {}).get("type") == "User"
        for comment in comments
    )


def api_json(path: str) -> tuple[object, str | None]:
    headers = {"Accept": "application/vnd.github+json", "User-Agent": "SubGaussianTailBounds-CI"}
    token = os.environ.get("GH_TOKEN", "")
    if token:
        headers["Authorization"] = f"Bearer {token}"
    request = urllib.request.Request("https://api.github.com" + path, headers=headers)
    with urllib.request.urlopen(request, timeout=30) as response:
        return json.load(response), response.headers.get("Link")


def resolve(event: dict, trusted_root: Path, fetch=api_json) -> dict:
    if "pull_request" not in event:
        return {"base_ref": "", "maintenance": False, "head_sha": ""}
    pr = event["pull_request"]
    repository = event["repository"]["full_name"]
    number = event["number"]
    head, base = pr["head"]["sha"], pr["base"]["sha"]
    if not REPOSITORY.fullmatch(repository) or not isinstance(number, int) or number < 1:
        raise ValueError("Invalid GitHub repository or PR number.")
    if not SHA.fullmatch(head) or not SHA.fullmatch(base):
        raise ValueError("Invalid GitHub commit SHA.")
    settings = json.loads((trusted_root / ".github/maintainers.json").read_text())
    maintainers = {name.casefold() for name in settings["maintenance_approvers"]}
    live, _ = fetch(f"/repos/{repository}/pulls/{number}")
    if live["head"]["sha"] != head:
        raise ValueError("This CI event is stale; run CI for the latest PR commit.")
    comments = []
    for page in range(1, 101):
        batch, links = fetch(f"/repos/{repository}/issues/{number}/comments?per_page=100&page={page}")
        if not isinstance(batch, list):
            raise ValueError("Unexpected GitHub comments response.")
        comments.extend(batch)
        if not links or 'rel="next"' not in links:
            break
    else:
        raise ValueError("Too many comments to establish maintenance authorization.")
    return {"base_ref": base, "maintenance": maintenance_comment(comments, maintainers, head),
            "head_sha": head}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--event", type=Path, required=True)
    parser.add_argument("--trusted-root", type=Path, required=True)
    args = parser.parse_args()
    context = resolve(json.loads(args.event.read_text()), args.trusted_root)
    output = os.environ.get("GITHUB_OUTPUT")
    if output:
        with open(output, "a") as stream:
            stream.write(f"base_ref={context['base_ref']}\n")
            stream.write(f"maintenance={'true' if context['maintenance'] else 'false'}\n")
    print(json.dumps(context, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"CI context failed: {error}", file=sys.stderr)
        raise SystemExit(1)
