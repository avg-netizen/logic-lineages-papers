#!/usr/bin/env python3
"""Build the canonical paper.tex. Requires Tectonic or pdfLaTeX."""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--online", action="store_true",
                        help="allow Tectonic to fetch missing TeX resources")
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    if shutil.which("tectonic"):
        cmd = ["tectonic", "--untrusted", "--keep-logs"]
        if not args.online:
            cmd += ["--only-cached"]
        cmd += ["paper.tex"]
        runs = 1
    elif shutil.which("pdflatex"):
        cmd = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
               "-no-shell-escape", "paper.tex"]
        runs = 3
    else:
        sys.exit("Install Tectonic or pdfLaTeX before building.")
    transcript = []
    for _ in range(runs):
        result = subprocess.run(cmd, cwd=here, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        transcript.append(result.stdout)
        if result.returncode:
            (here / "build-output.txt").write_text("\n".join(transcript))
            print("\n".join(result.stdout.splitlines()[-25:]))
            return result.returncode
    (here / "build-output.txt").write_text("\n".join(transcript))
    print(f"Built {here / 'paper.pdf'}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
