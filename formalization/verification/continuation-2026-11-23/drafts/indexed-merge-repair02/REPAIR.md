# Indexed policy merge repair 02

- Failed native gate: LogicLineages.StandardControlCurrent.PolicyIndexedMergeStatementChecks
- Failed native log label: merge-rank; receipt 1795422928589791736-5
- Failed original native log SHA-256: d5eb4ac8e4e8cc4abbeec37b425990d1b3dcfe153ddb8567f42321552984b6b9
- Failed proof path: LogicLineages/StandardControlCurrent/PolicyIndexedMergeProof.lean
- Reversible failed copy: PolicyIndexedMergeProof.lean.failed-source
- Failed leaf SHA-256: a992e846978cff193caca9a1ad416eca248bac544c89bb9726e34b98b7dff1fb
- Repaired leaf SHA-256: bffc213dcbf1d665d9bc0e9f9acfbe892090d1dcf5e23959c88341c6931bb607
- Unchanged targets SHA-256: 74038e1775436c57e823e497fe15c2770503c2bcb003288600c884d4757fedcf
- Unchanged checks SHA-256: 0a8fd7187263df32d61a5d7774b46c6d86f9832b074e6c07568d28d5926cee5f

Expose the exact original option bind before the coordinate case split, keeping
both List.getD operands literally the same. Rewrite effectivity targets with the
two shallow equations rather than asking application elaboration to infer their
function equality under nested product projections. Checker settings unchanged.
