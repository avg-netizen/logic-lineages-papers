# Internal signed Bézout existence: accepted supporting component

All six frozen main targets compile through exact aliases. Four arithmetic/decomposition supplier aliases also compile. All printed axiom closures contain only `propext`, `Classical.choice`, and `Quot.sound` (some suppliers omit choice). This is a supporting component, not a completed numbered paper theorem.

## Exact result

For arbitrary positive inductive body, arbitrary free-variable type, arbitrary ordinary arithmetic terms `a,b`, the original internal calculus proves existence of a least positive signed combination of `(succ a,b)`. A signed combination is literally four existentially bound natural coefficients satisfying `x*A+y*B=d+(z*A+w*B)`. The least positive combination internally divides both generators, with explicit existential quotient witnesses. Consequently, the object-language assertion that every positive common divisor is one implies existence of the signed unit combination. There is no assumed certificate-existence premise and no semantic natural-number reflection.

The proof uses the existing internal least-number theorem, genuine finite-block witness introduction/elimination, internal semiring identities, beta division at index zero, and an internally proved zero-or-successor decomposition. Positive nonzero remainders contradict leastness; zero remainders produce the quotient witnesses. Generator exchange supplies the second divisor.

## Boundaries

The result assumes the first generator is a successor and allows any second generator. Conversion from the signed unit equation to the existing oriented CRT certificate `1+u*A=v*B` remains pending. So do the later internal CRT/coding consumers and the full paper theorem. Existing accepted files were not changed; publication is handled separately by the coordinator.

## Evidence

- `FROZEN.sha256`: original definitions and four main target definitions, frozen/compiled before proof authoring. Initial target elaboration repair was only namespace/type qualification; failed candidate retained.
- `BEZOUT-FROZEN.sha256`: two further existence targets, frozen separately before their proof authoring; target compile receipt `build-reports/1794002387988630968-5.json`.
- `arithmetic/` and `zero-remainder/`: separate frozen arithmetic/decomposition targets, correspondence, and retained failures.
- `SOURCE-HASHES.json`: all 14 new Lean source hashes.
- `RECEIPTS.json`: all target, failed candidate, repair, and successful gate receipts.
- `final-gate-01.log`: six exact main aliases and standard-axiom checks; receipt `build-reports/1794002495989910345-7.json`.
- Supplier exact aliases passed in receipts `1794002113169739615-6` and `1794002353215526540-7`.

Every compiler invocation used the prescribed serialized script with 2048 MiB heap, 1536 MiB RSS, and 2048 MiB minimum free-memory limits. No full-root or remote-CI build is claimed. Independent read-only review accepted all fourteen sources, six main exact aliases, four supplier aliases and recorded frozen/repair provenance. The coordinator recursively matched all 784 focused sources to durable successful native receipts/logs. Peak across cited successful receipts is 1,226,832 KiB. This closure matching is separate from independent source review, not a fresh full rebuild.
