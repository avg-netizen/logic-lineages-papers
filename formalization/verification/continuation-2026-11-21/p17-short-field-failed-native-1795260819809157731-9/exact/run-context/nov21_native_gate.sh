#!/usr/bin/env bash
set -euo pipefail
cd /workspace/scratch/d6452c0f74c7/formalization-resume-20261121/formalization
export PATH=/workspace/scratch/d6452c0f74c7/recovery-toolchains-20261121/lean-4.32.0-rc1-linux/bin:$PATH
exec python3 scripts/check.py --timeout 180 --cpu-seconds 90 --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 --threads 1 "$@"
