# Paper 16 external tagged operators, local native recheck

At source revision `3dd39b57a`, Lean checked all eight external-operator contracts against the recovered Paper 16 comparators. All eight packet modules, including the stages proof repaired after the cloud failure, compiled from source in this run. The recursive closure comprises 178 modules compiled here and 19 source- and object-matched native cache hits.

The proof retains the scalar and multiset domains in equation (A) of `sections/ordinals.tex`. Its least predicates project to their two component predicates. On admitted codes, each least predicate characterizes accessibility for the corresponding original relation. For any well-founded index relation, tagged and standalone stages agree at the same index. A minimal stage applies the operator to the empty predicate. The numbered arithmetic-accessibility lemma still requires an internal arithmetic definition and an ID₁ proof for every well-typed term.

## Evidence

- The sole compiler command was `python3 scripts/check.py --core-profile LogicLineages.PersistentMarking.NumberedWindowExternalIDOperatorChecks`. Both existing locks and the default single-thread core limits applied. Peak process-tree RSS was 514,272 KiB against a 524,288 KiB cap. The bounded run ended and the previous host-local run control was restored.
- The local evidence exporter verified 197 modules against current sources, objects, input keys and receipts, 48 frozen source hashes, and eight exact axiom audits. A separate comparison verified all five author-source hashes in the recovered manifest. Each alias used only the standard foundations recorded in its audit. [Recursive local evidence](NUMBERED-WINDOW-EXTERNAL-ID-OPERATORS-LOCAL-EVIDENCE.json) (SHA-256 `9cbf55e4a326873728d3da239669655f70c19140f613ac3acc1c1ab26cd0bfc8`).
- The new native receipt has SHA-256 `7b8dc1b11443f5e988fdd450c9def916c4f3430e9847ceba4c87484cfe2ec0cc`. The eight-alias log has SHA-256 `3093f5b9308e81ae59187c41e5979e7561bece8613055285583bf33b4b901d37`. [Local native receipt](external-id-operators-local-native/1795126084445850887-10.json) · [Exact alias log](external-id-operators-local-native/1795126084445850887-10-LogicLineages-PersistentMarking-NumberedWindowExternalIDOperatorChecks.log)

The worker submitted this evidence to the coordinator for independent source and artifact review. The numbered register totals 149 checked and 18 pending. The cloud-loss handoff retains the history of the unavailable original native artifacts. [Cloud recovery handoff](../../recovery-nov19/CLOUD-LOSS-1511-HANDOFF.md)
