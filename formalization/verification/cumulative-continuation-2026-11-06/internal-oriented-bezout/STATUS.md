# Checked internal oriented Bézout and binary CRT

Four exact aliases pass on unchanged frozen targets:
- InternalMultiplicationCommutativityStatementChecks.commutativity_exact.
- InternalOrientedBezoutStatementChecks.conversion_exact.
- InternalOrientedBezoutStatementChecks.existence_exact.
- InternalBinaryCRTStatementChecks.binaryCRT_exact.

The signed equality x*A+y*B=1+(z*A+w*B), with A=succ(a), B=succ(b), yields the literal certificate succ(u*A)=v*B, where u=(z+x*b)+w*B and v=(x*A+y)+w*a. All arithmetic is proved using derivation constructors and PA induction, not semantic reflection. Existential elimination of the existing signed Bézout theorem gives oriented certificate existence from the original object-language coprimality. The existing explicit CRT combination then gives one existential c satisfying both original congruences for arbitrary residue terms.

The supplier aliases use only propext and Quot.sound. The two existence aliases additionally use Classical.choice, inherited through internal logical derivation construction. No new axiom, sorry, admit, native_decide, semantic Nat reflection, or certificate premise replacing coprimality was added.

All 14 new sources match successful bounded compiler receipts. Raw successful and failed receipts and logs are preserved in raw-receipts/. Failed syntax/consumer candidates are preserved beside them. Maximum observed process-tree RSS across this lane's attempts: 1,203,600 KiB. Every compiler used the required serialized helper with 2048 MiB heap, 1536 MiB RSS, 2048 MiB free-memory floor, one thread, 90-second CPU and 180-second wall limits.

Final focused entry: LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinaryCRTStatementChecks.
Final raw receipt: build-reports/1794003149894972541-5.json.

This closes binary internal CRT only. General finite-family assembly, beta-list coding, and the complete internal-level-two source consumer remain pending. No numbered whole-source register promotion, full-root build or remote-CI success is claimed. Existing files are unchanged. Independent review accepted all fourteen new sources, exact alias scope, frozen targets, repairs and successful receipt hashes. The coordinator recursively matched all 798 focused sources to durable successful receipts/logs; peak across cited receipts is 1,226,832 KiB. This is not a fresh full-root rebuild. Publication is handled separately.
