# Second isolated endpoint cap repair

Scalar ThresholdTailBridgeProof passed1794999292421487486-5. Isolated remaining ThresholdEndpointProof stopped at RSS1794999355947522613-5; source and receipt preserved, process reaped and ticket released, no retry.

Split remaining obligations into three proof modules:
- ThresholdCombinedTailProof: only combined-tail equality. Two separately typed inverse-tail equality facts use congrArg on the known raw subtraction-code equality; final max equality uses congrArg₂. No rewriting/unfolding giant raw programs in nested target.
- ThresholdGuardProof: actual proper gap, original norm guard and left/right tail bounds, unchanged statements/proofs.
- ThresholdEndpointProof: only actual H-hit program membership. Construct normal partner limit/hit by explicit equality transport, obtain checked fixedEntryProgram membership, then transport only the target-code argument with congrArg/ Eq.mpr. No tactic rewrite descends through the partial evaluator's membership implementation.

All declaration types, conclusions, premises, six frozen pins and caps unchanged. No full closure diagnostic authorized. First reviewed retry should target ONLY ThresholdCombinedTailProof; if passed, later separate tickets for guard/membership. Each resource stop requires preservation/release and further independent review before retry.

## Material dependency reduction (applied, uncompiled pending review)

The capped old endpoint inherited the entire actual inverse-table/equal-gap/initial-peeling proof chain through ThresholdNoteCodeProof, even though scalar endpoint arithmetic needs none of it. Removed those imports from the scalar lane; note arithmetic now imports only actual ordinal arithmetic code, raw norm correctness and actual norm calibration. Replaced its reliance on the heavy gapInputTailEffective theorem by a local exact normal encoded-gap-tail equality proved directly from four checked raw norm equalities and the unchanged literal tail definitions. This is actual same equation, not a new assumption.

Static local-source closure now: NoteCode85 modules/169588 bytes; TailBridge86/171767; CombinedTail87/173153; Guard88/174639. H-membership endpoint imports actual FixedEntryProgram only where needed,193 modules/486879 bytes. Actual InverseTableProof is imported later only by ThresholdUnequalProof, its genuine consumer. Full source comparator/supplier scope unchanged. This materially reduces the first endpoint trial dependency closure, not just file placement. Original baseline scalar bridge passed the larger imports, so both unwanted definitional unfolding and import size are addressed, without asserting an unmeasured unique cause.

## Reduced combined-tail native result
Parent ticket THR-COMB-1100: `ThresholdCombinedTailProof` passed, receipt
`build-reports/1794999648538211355-2.json`. This rebuilt the reduced
ThresholdNoteCodeProof and direct norm-derived ThresholdTailBridgeProof too.
Process reaped, queue released. Original six pins and caps unchanged.
No full threshold acceptance: guards, membership and final consumer closure
remain to be checked separately.
