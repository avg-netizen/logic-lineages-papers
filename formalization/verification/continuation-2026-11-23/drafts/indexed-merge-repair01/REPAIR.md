# Indexed policy merge repair 01

- Failed native gate: `LogicLineages.StandardControlCurrent.PolicyIndexedMergeStatementChecks`
- Failed native log label: `indexed-merge`; receipt `1795422788848681011-5`
- Failed original native log SHA-256: `2512aee34bebe2b35fd19a4098dbfe0f299d6b3334ebb5423039b54dd35bbc25`
- Failed proof path (relative to formalization): `LogicLineages/StandardControlCurrent/PolicyIndexedMergeProof.lean`
- Reversible failed copy: `PolicyIndexedMergeProof.lean.failed-source`, SHA-256 `d421422d2ade47aa405bf4a73849d26b11f7857a505605cff6b64f93ac5c096b`
- Repaired proof SHA-256: `a992e846978cff193caca9a1ad416eca248bac544c89bb9726e34b98b7dff1fb`
- Unchanged targets SHA-256: `74038e1775436c57e823e497fe15c2770503c2bcb003288600c884d4757fedcf`
- Unchanged checks SHA-256: `0a8fd7187263df32d61a5d7774b46c6d86f9832b074e6c07568d28d5926cee5f`

The branch parser now uses Bool.cond exactly. Named argument maps and shallow reflexive
equations separate effectivity from nested reduction, with proof-local irreducibility and
unchanged checker limits. The exactness proof rewrites a literal bind equation for the
original do branch and explicitly exposes the original coordinate step under its case split.
The original code definitions and checked scope are unchanged.
