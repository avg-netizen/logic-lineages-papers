#!/usr/bin/env python3
"""Produce recursive evidence for a new paper16 exact core pass without Lean."""
import argparse
import json
from pathlib import Path

from replay_owner_ready_core_evidence import HERE, PAPER, cloud_context, exporter, owner


def main():
    cli = argparse.ArgumentParser()
    cli.add_argument("receipt", type=Path)
    cli.add_argument("output", type=Path)
    cli.add_argument("aliases", nargs="+", help="namespace-relative exact aliases")
    cli.add_argument("--manifest", action="append", type=Path, default=[])
    args = cli.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(HERE), output
    manifests = [PAPER / "MARKED-CONSTRUCTOR-FROZEN.json", *(p.resolve() for p in args.manifest)]
    owner.compiler_context = cloud_context
    report = owner.verify(args.receipt.resolve(), args.aliases, manifests)
    evidence = exporter.export(report)
    with output.open("x") as f:
        f.write(json.dumps(evidence, indent=2) + "\n")
    print(exporter.digest(output), output.name,
          f"{evidence['local_modules']} recursive modules; {evidence['exact_aliases']} exact audits; "
          f"{len(evidence['source_pins'])} pins")


if __name__ == "__main__":
    main()
