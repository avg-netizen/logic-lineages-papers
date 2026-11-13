# Rank calibration continuation: not yet a completed target

Updated 13 November 2026, after original unsorted-child bound acceptance.

The frozen `RankMemoTargets.ActualSourceRankCalibration` remains unproved.
The new numeric decoder is proof-side only. Neither the original evaluator nor
any selected canonical tuple has been replaced.

## Verified prerequisites reported by coordinator

- Weighted insertion/sort exact2: 1794569876860672875-30.
- Observation numeric descent exact4: 1794574189086269565-5.
- Memo recurrence/table coherence and lookup coverage; final coverage receipt
  1794574934010882972-38.
- Memo lookupWeight exact helpers: 1794575306420580375-35.
- Identity-weight sum/entry bounds exact2: 1794575593003662334-54.
- Unsorted original BASE child-code bound exact2: 1794575970741643761-51.
- Memo dispatch, successor, source recursive-root recovery, strong-induction
  syntax and binding; opening helpers: 1794576104760271401-5.
- Local child weight via genuine strong IH: 1794576386949272076-53.

Accepted source bytes are immutable. Failed source/log/receipt snapshots are in
`drafts/`; no source failure was counted as acceptance merely because another
declaration printed an axiom audit.

## Authored, verification pending

BranchValue and Leaf repairs are pending after preserved failed runs. Selector,
RootEncoding, LambdaStep, ApplicationStep, and the source-lambda coordinate and
query chain are also pending. The top source-lambda candidate is
`RankCalibrationLambdaProof.actualLambda`: original source + actual successor
E-code + actual raw rank + literal lambda tag + BelowRaw induction hypothesis
imply the decoder gives that same rank. It contains no child-source, child-rank,
child-decoder, table-correctness, or desired envelope premise.

## Remaining proof work

- Check and repair the authored source-only successor lambda branch.
- Assemble corresponding original application and leaf/zero branches.
- Integrate the independently owned argument-rank aggregation with actual BASE
  and extras admission, discharging AllSmall using the accepted unsorted/stored
  strict child-code bounds and LocalWeights using genuine source-child IH.
- Discharge the strong induction and all original source tag cases, then check
  the unchanged full calibration target and standard-axiom audit.

Code zero is a total decoder fallback of one. This does NOT assert an admitted
full evaluator output of zero exists; a zero recursive-root observation is not
a zero full evaluator envelope. The variable zero branch is conditional only.

Full paper06 I/C and canonical Object covariance remain pending. Numeric rank
calibration, even if completed later, does not by itself identify the evaluator
with the retained structural key or establish raw canonical erasure fixedness.
