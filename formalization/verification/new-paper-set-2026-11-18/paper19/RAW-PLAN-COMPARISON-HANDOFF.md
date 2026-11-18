# Literal raw Plan comparison outputs

**READY-FOR-ROOT-REVIEW**.

Native receipt `1795033707661374274-124` compiled the exact root before the combined
gate reached a separate unverified binary proof. Dedicated union
receipt `1795033818044979271-36` passed. Recursive evidence matches 187 modules,
with zero errors and all 3 exact aliases using only permitted
standard axioms. All 8 frozen pins match.

On every typed Plan, the raw compiler produces the exact strict and weak
 comparison DAG pairs. Arbitrary raw success reconstructs one complete
 typed Plan with the same literal output codes. The joint computation uses
 the verified Plan forest, the literal aggregate and actual upper/lower
 wrappers. Both ordinary elaboration failures and exact proof text are
 preserved under `raw-plan-comparison-failed/`.

SHA-256

- `RAW-PLAN-COMPARISON-EVIDENCE.json` 32a05b1b244847843976a268a7640515a9d5af0e640f517bf39e67c2c87bec24
- `RAW-PLAN-COMPARISON-BUILD-RECEIPT.json` 3d6384d0e5db95a071622f02758542223c3380a0e86648b60b74ce3ee10a015f
- `RAW-PLAN-COMPARISON-NATIVE-PROOF-RECEIPT.json` e073dc02cd04e031795df2cb056e161d04b0871040ed85a1fc1dd6d1086b1f2d
