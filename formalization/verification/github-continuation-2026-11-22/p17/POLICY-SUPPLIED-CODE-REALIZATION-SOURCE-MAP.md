# Supplied policy codes cover the existing effective policy class

Baseline: `dd4eddff9f8eab0a4532e8df4880f71b8d5dffb9`.

This is a bounded continuation of `POLICY-SUPPLIED-CODE-MACRO-SOURCE-MAP.md`.
Its source purpose is the supplied-policy uniformity clause of Paper 17
`thm:main` and the computable selector in `def:literal-policy`.

The new target module is
`LogicLineages/PermittedControl/PolicySuppliedCodeRealizationTargets.lean`.
It imports the previously frozen macro-interpreter target and preserves its
`RealizesPolicy` relation without modification.

- `EffectiveHasCode` states that every policy satisfying the existing
  `PolicyShape.Effective` predicate has an ordinary `Nat.Partrec.Code`
  computing its same literal selector, on paired site-and-arity inputs.
- `RealizedIsEffective` states the converse, retaining the original
  `PolicyShape.Effective` predicate and its original input/output encodings.
- `ExactPolicyCodeRealization` exposes the resulting equivalence.

The intended suppliers are the pinned Mathlib `Code.exists_code`,
`Code.eval_part`, and the existing encoding/composition closure rules.
These statements ensure that the macro interpreter's realization premise
does not reduce the admitted policy class. They do not select a code
computably from an arbitrary semantic policy and do not claim that
`thm:main` is complete. The source/compiler bridge and uniform comparison
program remain separate obligations.

Targets and this source note are hashed in the lane ledger before proof
authoring. Root owns the only native compiler queue. No compiler or Git
operation is authorized for this lane.
