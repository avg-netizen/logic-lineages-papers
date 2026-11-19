# Whole-tuple material elaboration split (new modules only)

The reviewed monolithic `NumberedWindowTupleAuxProof` was resource-stopped
by the original core RSS limit after 69 rows passed. Receipt
`1795074636197725779-6` observed 529896 KiB at the failed leaf, vs the
unchanged 524288 KiB cap. There was no Lean proof diagnostic and no claim
of the final numbered theorem. All five originally proposed proof sources,
the freeze and exact receipt/log are archived. The stopped Aux and old root
also remain byte-identical in the active source tree.

The new candidate uses **the same frozen WholeTupleSimulation** and the
same validated literal raw window/apply semantics and supporting lemmas.
Its source changes are append-only:

| New module | Actual proof work moved out of the heavy recursion |
| --- | --- |
| `NumberedWindowTupleAuxGoals` | Exact original generalized predicate regrouped as AtArgs (fixed actual q and suffix) and ForArgs (all actual q at that suffix). Same single actual `applyAux q args values = some r`, original typed/context/admissibility guards, paired images and unchanged n+length+1 threshold. Shared literal substitution-window bridge and genuine nil suffix path. |
| `NumberedWindowTupleAuxHeadCases` | At original ordinary or marked functional head, prove actual typed `consumeTypes` and read that whole exact branch. Call the already compiled ordinary/numbered path supplier with actual original substituted base/extra pairs. A marked source retains k and must cover n+remaining tuple length. |
| `NumberedWindowTupleAuxLambdaCase` | At a literal lambda constructor, use the actual next parameter type and prepend both same concrete argument images to their old original blocks. The only induction premise is the same normalized ForArgs goal at the actual remaining suffix. Literal beta supplies the actual push-block equality, and the same function-only context transports it through all remaining args. |
| `NumberedWindowTupleAuxFoldProof` | Structural recursion on the original `Spine.Args.tail` only. Call the real nil and original shape branches; reject protected-variable overapplication by the original undefined branch of `applyAux`. No dependent well-founded recursion over the large source/argument/image proof bundle. |
| `NumberedWindowTupleSplitChecks` | Same exact final `WholeTupleSimulation` for arbitrary original symbolic sources including marks, with no additional hypothesis; literally identical exported theorem proof except the changed import/namespace and call of the structural fold with reordered matching arguments. |

Total candidate closure is 74 vs 71; the old failed Aux leaf is **not** in
the new closure. The material change is eliminating simultaneous heavy
branch elaboration and generated well-founded recursion in one leaf. Closures
of shared goals/head branches/lambda branch are 67/70/69, and the final fold
only performs data-structural cases. No change to checker/profile or frozen
comparator, active source, original witness, budget, contexts or raw paths.
Neither the old resource-stopped proof nor this new proposal claims the
numbered endpoint until a complete independently reviewed exact pass.

## Candidate SHA-256
db9fe40d34c1188a88882e5bdc6ed38d6998d912b57fddeb71ed7c580abfdc02  LogicLineages/PersistentMarking/NumberedWindowTupleAuxGoals.lean
4bdbfc2e6cb5220748dac0486c6d6c01515705213fd7fbd4889adf5bd027a845  LogicLineages/PersistentMarking/NumberedWindowTupleAuxHeadCases.lean
b5c3bd3eafce82d5c96052736016e7e915634e8c2eb0dc3a524344b7864a47ff  LogicLineages/PersistentMarking/NumberedWindowTupleAuxLambdaCase.lean
a5ecb1634a46706b438cd7cb7859c7cb348ea9010ea1e469473089e8386e5886  LogicLineages/PersistentMarking/NumberedWindowTupleAuxFoldProof.lean
7069d9006164e9699048b873be405c45b94348f933209a747120276fcc7a82b2  LogicLineages/PersistentMarking/NumberedWindowTupleSplitChecks.lean
