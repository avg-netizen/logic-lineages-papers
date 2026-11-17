# Independent EraseInvariant syntax repair review

Static source review approved; native acceptance pending.

All nine complete original public theorem headers, including simp annotations,
are byte-identical to the saved original. Independently verified saved original
SHA256 and EraseInvariantDefinitions byte identity against HEAD.

The seven schema definitions specialize exactly to the original definitions at
C = ArgumentEntryCount.count and S = Erase.state, modulo whitespace and redundant
parentheses around predicate. Generic proofs establish only syntax substitution,
renaming, witnesses and binder identities using existing lemmas. Original wrappers
specialize to those exact Programs with no extra assumptions. countEffectWitness
correctly has no S parameter, since S does not occur in its type. Binder order,
implication polarity and original object-language equality are retained. Local
programGraph irreducibility changes elaboration only. No semantic/count/induction
oracle or added preservation hypothesis is present.

No compiler or proof-source edits by this reviewer. This is memory refactoring,
not new mathematics. Final fixed-cap native and axiom/source evidence are pending.

## Native reconciliation

Receipt 1794929158269397442-5 has zero failing module rows under the original
2048 MiB heap / 1536 MiB RSS / 2048 MiB free / 180 s wall / 90 s CPU / 1 thread
profile. All three repair module source hashes match current bytes. Inspected
logs contain no errors or sorryAx; generic and original namespace audits are
standard-only. This accepts the repair only, not downstream metadata closure.
