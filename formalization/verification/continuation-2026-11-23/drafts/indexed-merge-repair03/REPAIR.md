# Indexed policy merge repair 03

- Failed native gate: LogicLineages.StandardControlCurrent.PolicyIndexedMergeStatementChecks
- Failed native log label: indexed-merge-repair02; receipt 1795423024483204122-18
- Failed original native log SHA-256: 3af50d5a4b2f84d44460674f36b768e8bd28844af81ebeab94f361143368b3c6
- Failed proof path: LogicLineages/StandardControlCurrent/PolicyIndexedMergeProof.lean
- Reversible failed copy: PolicyIndexedMergeProof.lean.failed-source
- Failed leaf SHA-256: bffc213dcbf1d665d9bc0e9f9acfbe892090d1dcf5e23959c88341c6931bb607
- Repaired leaf SHA-256: 7efd64fc9814388df89a87a81d17dde9f5745c35861687aeb81c2518f72e9d85
- Unchanged targets SHA-256: 74038e1775436c57e823e497fe15c2770503c2bcb003288600c884d4757fedcf
- Unchanged checks SHA-256: 0a8fd7187263df32d61a5d7774b46c6d86f9832b074e6c07568d28d5926cee5f

Native repair02 cleared the full semantic coordinate and range proofs. For its
only remaining effectivity equality failures, split the Option scrutinees
explicitly (under function congruence for the Part.bind continuation),
so that reflexivity sees concrete branches and reduces their product projections.
Checker settings, definitions and checked statements unchanged.
