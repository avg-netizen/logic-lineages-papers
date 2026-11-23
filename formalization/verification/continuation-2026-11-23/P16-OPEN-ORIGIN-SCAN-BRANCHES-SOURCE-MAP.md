# Paper 16: preserve both side-local accepting scans across an allocation step

The same original tag-4 row and positive certificate report is allocated
exactly on one side, looking up membership in the same fixed scratch
left removed pool in both complementary filters. At a left hit, the
left output is the literal old row cons and the right output equals
its existing tail. At a left miss and right hit, the opposite holds.
Given both side parses, the two existing accepting tail scans and the
actual step graph reports, both new side scans are then constructed in
the original calculus. The chosen row is tested against that side's
original raw removed code and its untouched dominator/positive tuple.

Exact gate `LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanBranchesProof`,
alias `exact_OpenOriginScanBranches`. This is the local simultaneous
cons step on supplied branches and genuine step reports. The existence
of a side membership, arbitrary-length induction, counts and output
re-encoding are separate.

Frozen Lean source hashes (SHA-256):

    5012f98b7a23f91e496cbd500780983762ba098f04ff861f713f0bc795eceaf4  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalOpenOriginScanBranchesProof.lean
    1fe7cbca092180d3e72365ecedc66a14096a4e179571c2476d288a6e044f5d1c  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalOpenOriginScanBranchesTargets.lean
