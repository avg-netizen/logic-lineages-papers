# Internal beta pair arithmetic

Accepted supporting arithmetic component; this does not establish beta pair existence by itself.

Frozen exact targets were compiled before any proof authoring. Parent definitions and targets compiled first (receipt `build-reports/1793999933508884964-6.json`). The initial arithmetic target used an incorrect Formula namespace and was preserved as `failed-target-v1.lean` with its log. Corrected targets, including the requested bound equation, froze and passed in `build-reports/1793999998890913115-9.json`.

The accepted proof and all four exact aliases pass in `build-reports/1794000144014444309-8.json`. Every alias depends exactly on `propext` and `Quot.sound`. Peak process-tree RSS in the successful proof/check run: 1204556 KiB. Heap 2048 MiB, RSS 1536 MiB, free-memory floor 2048 MiB, one compiler thread. No full-root or remote-CI claim.

## Public derivation API

Namespace `InternalBetaPairArithmeticProof`, implicit arbitrary body, variable type and original context Gamma:
- `pairEquation x y`: firstCode x y equals secondQuotient y multiplied by the successor of twice(secondCode x y), plus y.
- `boundEquation x y`: y + successor((x+x)+y) equals successor((x+y)+(x+y)).
- `oneMul t`: successor(0) multiplied by t equals t.
- `twoMul t`: successor(successor(0)) multiplied by t equals twice t.

These construct original Derivation trees from established original multiplication laws and addition associativity/commutativity/congruence. The finite reorder proof expressions were generated syntactically; there is no semantic reflection or evaluation of arithmetic values. `generate.py` preserves the initial generator; two failed proof snapshots/logs preserve the original namespace ambiguity/heartbeat failure and missing commutativity namespace. The accepted source disambiguates original equality proof constructors and opens the established addition cancellation namespace. No target mathematics changed.

`accepted-source.sha256` records accepted source hashes; `frozen-target.sha256` records the pre-proof target freeze. No commits made.
