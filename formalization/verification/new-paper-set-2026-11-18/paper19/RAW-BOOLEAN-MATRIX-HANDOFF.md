# Exact raw Boolean matrix lowering

**READY-FOR-ROOT-REVIEW**.

Preflight `1795033549473634632-70` compiled the frozen target. Native proof
receipt `1795034793600863744-104` compiled both exact aliases, before the
combined gate stopped at the subsequent input-state proof. Dedicated
closure gate `1795034839816064799-20` passed. The recursive evidence
matches 244 modules and has no errors. Both exact aliases and the
inherited audits use only permitted standard axioms. All nine frozen
source pins match.

All six literal Boolean nodes lower to the actual constraint lists,
with real predecessor and natural-slot indices, one global bit and
auxiliary block and the common one. The reverse row fold exactly matches
the typed DAG traversal. The exact matrix contains the original witness
binders and root equality. Raw numeric/list lowering is primitive
recursive. The separate frontend validates the source syntax that feeds
these structural operations.

Failed proof text and native receipts are preserved under
`raw-boolean-matrix-failed/`. Proof repairs materialize finite row lists,
transport concrete offset equalities and specify primitive projection types.

SHA-256

- `RAW-BOOLEAN-MATRIX-EVIDENCE.json` 45dbc605aae406270657ba18624ae612c58062d2d5bc99c1744908ea047b6092
- `RAW-BOOLEAN-MATRIX-BUILD-RECEIPT.json` 03ccf9dc78c7434a8e68c2009bdd8930f94c702f7030b8143da7c7a96dd46c8e
- `RAW-BOOLEAN-MATRIX-NATIVE-PROOF-RECEIPT.json` 0b7ed8ed8d91fe5291f23ab80bc123b5dfd73c10690d704e70fda9e3c9c96bd1
- `RAW-BOOLEAN-MATRIX-TARGET-PREFLIGHT.json` c338096660738550426e50968abbafa5476384e3b42974bb2ace0e00a2458791
