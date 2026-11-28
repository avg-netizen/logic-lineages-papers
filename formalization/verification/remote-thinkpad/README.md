# Running the Lean checker on the ThinkPad

Set up 27 November 2026, after this host ran out of memory for the checker's 2048 MiB floor.

`tp.sh` runs the repository's own `scripts/check.py` (same flags and caps as the local gate) on a second
machine on the LAN (a ThinkPad: 12 threads, 23 GB RAM) and brings the results back. The address is read from
`TP_HOST` or from the git-ignored one-line file `host.local` (`user@address`).

```sh
bash verification/remote-thinkpad/tp.sh status
bash verification/remote-thinkpad/tp.sh gate LogicLineages.NativeModule.PersistentMarking.SomeProof [more modules]
```

`gate` = push newer sources, objects and receipts → run there → pull new objects, receipts and logs.
`push`, `pull` and `setup` are also available separately; each run leaves a log in `logs/`.

## How it works

- `check.py` keys its cache on absolute paths (compiler, `LEAN_PATH`, every imported object, receipts). The
  ThinkPad therefore mirrors the **same absolute paths** under the same user: this `formalization` directory,
  the pinned package objects (real path of `.lake/packages`), and `~/.elan` with the pinned toolchain. A
  module checked on either machine is then a verified cache hit on the other.
- Only compiled objects of the packages are mirrored (6.1 GB), not their sources; the toolchain is copied,
  not downloaded, so the compiler bytes are identical.
- The remote job runs as a transient systemd user scope: `nice 19`, `CPUWeight=20`, `MemoryMax=6G`
  (`TP_MEMORY_MAX` to change), and refuses to start on battery (exit 77). `check.py`'s own limits are
  unchanged: one Lean process at a time on that machine, RSS cap 1536 MiB, free-memory floor 2048 MiB.
- Nothing is deleted on either side. Sync is "newer file wins" (`rsync -u`).

## Checked on set-up

| Test | Result |
| --- | --- |
| Remote gate on an already-checked module | 1,573 cache hits, 0 compiled, 7 s |
| Remote gate on three never-compiled modules | all three compiled and passed, 14 s, receipt `1795842164430545753-2237658` |
| Local gate on the same root afterwards | 2,271 cache hits, 0 compiled — the local checker accepts the ThinkPad's objects |

## Limits and cautions

- The laptop must be awake, on the LAN and on mains. The SSH session carries the job: if the connection
  drops, the run stops (completed modules keep their receipts; rerun `gate`).
- A receipt does not record which machine produced it; the wrapper's log in `logs/` does.
- If the toolchain or `lake-manifest.json` changes, rerun `tp.sh setup`.
- If the same module is compiled on both machines at once, the mixed objects simply fail the digest check
  and are recompiled; a false cache hit is not possible.
- The mirror on the ThinkPad lives at the same absolute path as this checkout, about 10 GB, plus `~/.elan`
  (2.8 GB).
- `gate` waits (default 30 minutes, `TP_WAIT_SECONDS`) when another checker holds the remote lock or the
  remote free-memory floor is closed.
- The lane wrapper `gate.sh` is unchanged; to send a lane's gate to the ThinkPad, call `tp.sh gate …`
  instead of `gate.sh mathlib …`.
