# Internal types continuation ledger

## Source inspection and scope approval

Base: `9a8fd8f8ffd9c1ab27b91096dc1e52aa196bb413`. User-facing continuation date: 22 November 2026, America/Chicago. UTC timestamps below may fall on 23 November.

The original all-type checker is obtained as a primitive-recursive program witness; its numeric calibration alone is not an accepted arbitrary-open inversion proof. The existing G05 analysis identifies literal finite-list membership elimination as a missing internal ingredient for the grammar codomain rule.

Root approved: exact internal literal finite-list membership equivalence, finite actual-program guard/image transfer, and grammar codomain inversion derived from explicit finite numerical closure. Original `scratchMember`, `cellTail`, `TV` and `T` are preserved. No refitted replacement in the actual type-checker slot and no unrestricted numerical-reflection inference.

New target files:

- `LogicLineages/PersistentMarking/NumberedWindowInternalLiteralTypeMembershipTargets.lean`.
- `LogicLineages/PersistentMarking/NumberedWindowInternalGrammarCodomainTargets.lean`.

Source map: `verification/github-continuation-2026-11-22-round3/internal-types/INTERNAL-TYPES-SOURCE-MAP.md`.

These files precede proof authoring. Freeze hashes and UTC timestamp follow in the next entry.

## Frozen statement checkpoint — 2026-11-23 05:20:05 UTC

The two target modules and source map existed before any proof module in this packet. Their SHA-256 hashes are frozen:

| File | SHA-256 |
| --- | --- |
| `LogicLineages/PersistentMarking/NumberedWindowInternalLiteralTypeMembershipTargets.lean` | `fb41b63bb1d132b66979bce426eb4f3509f38df59fab4dbf71b3ca36ffd27611` |
| `LogicLineages/PersistentMarking/NumberedWindowInternalGrammarCodomainTargets.lean` | `ba40bbdde6d2225f71cf7c81ff39b9f2d61cf9551f96f16c9c3fe83c121ff1a7` |
| `verification/github-continuation-2026-11-22-round3/internal-types/INTERNAL-TYPES-SOURCE-MAP.md` | `41cc8863e783f6feb8f5a31212c4ad63511ce6325fb6d5418952197eff9dba95` |

Native exact-type/axiom status is pending. The root coordinator alone will run the fixed-limit gate.

## Initial proof submission — 2026-11-23 05:23:21 UTC

Root reports that the two frozen Targets modules passed unchanged in gate03, receipt `build-reports/1795411295477093868-11.json`. This target-only result is not acceptance of the new proofs.

The proof packet constructs original scratch-membership cons elimination, finite literal-list equivalence, concrete numeral branches for actual-program guard/image transfer, and the actual sparse `cellTail` grammar rule. Initial proof hashes:

| File | SHA-256 |
| --- | --- |
| `LogicLineages/PersistentMarking/NumberedWindowInternalLiteralTypeMembershipSupportProof.lean` | `d85e1177668ad8e40e6787b2044a12491a76f6934bf5e70caf0dc8f5a5940b21` |
| `LogicLineages/PersistentMarking/NumberedWindowInternalLiteralTypeMembershipProof.lean` | `c3e2700d184282166d8341582f75068d94c5caf431f7a9fdf1f4d9c312c0b88c` |
| `LogicLineages/PersistentMarking/NumberedWindowInternalGrammarCodomainProof.lean` | `db9cc902b8f7a0014726c083fb5e5552a377f09d394955537a9cb4cfbf1d970f` |

Both targets and the source map retain their frozen hashes. The seven exact aliases and their axiom prints are ready for the root's sole native gate. No compiler or Git action occurred in this lane.

## Gate04 repair — 2026-11-23 05:25:11 UTC

The first proof gate failed in SupportProof, receipt `build-reports/1795411459140097566-11.json`. The raw module log reports two unresolved projection-vector arguments and two public-declaration references to privately imported `consGraph`. Main membership and grammar proofs were not reached; downstream recovery placeholders are unaccepted.

The exact submitted SupportProof (`d85e1177668ad8e40e6787b2044a12491a76f6934bf5e70caf0dc8f5a5940b21`) was copied before repair to `failed-drafts/1795411459140097566-11/NumberedWindowInternalLiteralTypeMembershipSupportProof.lean.txt`. The proof-only repair supplies explicit original input vectors and `Fin 3` indices, and publicly imports the unchanged standard list-codec support module for the exposed cons helper statements. Repaired support SHA-256: `2063a1509c225634de471c3658779ba52ba521dbc50d4c49ab7187cdcabb98e1`. No frozen targets or source map changed.

## Gate06 repair — 2026-11-23 05:27:20 UTC

The next proof gate, receipt `build-reports/1795411555705351694-11.json`, reduced the support diagnostics to the literal cons-cell final simplification: the original encoder's successor notation and program evaluation's addition-by-one notation remained across the `consGraph` abbreviation. The submitted support bytes (`2063a1509c225634de471c3658779ba52ba521dbc50d4c49ab7187cdcabb98e1`) were preserved at `failed-drafts/1795411555705351694-11/NumberedWindowInternalLiteralTypeMembershipSupportProof.lean.txt` before repair.

The only source edit unfolds `consGraph` in that simplification and includes `Nat.succ_eq_add_one`. Updated support SHA-256: `d81f13e9d58c5ffca3a9723ab7480ac8ad0c98079195b65e8101a72c29eb69b0`. The main/grammar proofs, frozen targets and map remain unchanged. Native proof acceptance remains pending.

## Gate07 repair — 2026-11-23 05:29:39 UTC

Receipt `build-reports/1795411723880947984-11.json` leaves only the literal-cons tape equality: the numeral graph had vector notation while the original `consGraph` uses nested `Fin.cons`. Submitted support `d81f13e9d58c5ffca3a9723ab7480ac8ad0c98079195b65e8101a72c29eb69b0` is preserved at `failed-drafts/1795411723880947984-11/NumberedWindowInternalLiteralTypeMembershipSupportProof.lean.txt`.

The existing extensional `tape` proof now targets the original nested `Fin.cons` function directly, using the same `funext` and finite-index cases. Repaired support SHA-256: `686d49d31127a3df074bd72d62e9b4b6775611692054ef0b53cb3beadcd57123`. No mathematical statement or other proof module changed.

## Gate08 main repair — 2026-11-23 05:33:05 UTC

Receipt `build-reports/1795411941242954089-11.json` passes SupportProof at hash `686d49d31127a3df074bd72d62e9b4b6775611692054ef0b53cb3beadcd57123`. The main module prints standard-only dependencies for literal membership, generic finite guard/image transfer, and the actual-type instance. Its remaining error is a rewrite in the refit instance: the supplied calibration is phrased through the existing `run` abbreviation, while the goal uses `evaluate`. The module as a whole is not yet accepted, and the refit endpoint's recovery `sorryAx` is unaccepted. Grammar has not been reached.

Initial main proof `c3e2700d184282166d8341582f75068d94c5caf431f7a9fdf1f4d9c312c0b88c` was preserved at `failed-drafts/1795411941242954089-11/NumberedWindowInternalLiteralTypeMembershipProof.lean.txt`. The proof-only repair states that same calibration equality directly with `evaluate` before rewriting. Repaired main SHA-256: `ab41683cc043a3b922c6f1c4a016bb95006fc40db488ca8b8e0faf84888a90b7`. Passed support, frozen targets/map and grammar proof remain unchanged.

## Final native success — 2026-11-23 05:33:53 UTC

Root gate09 passed all requested membership and grammar modules. Receipt: `build-reports/1795412014343677355-11.json`. The corresponding main and grammar module logs print exactly `propext`, `Classical.choice`, and `Quot.sound` for each of the seven exact aliases, with no recovery axiom. Native Lean establishes proof validity; this packet uses the prior source/statement scope check and the recorded exact native/axiom gate, without a duplicate proof-body acceptance review or native replay.

Final accepted proof hashes:

| File | SHA-256 |
| --- | --- |
| `LogicLineages/PersistentMarking/NumberedWindowInternalLiteralTypeMembershipSupportProof.lean` | `686d49d31127a3df074bd72d62e9b4b6775611692054ef0b53cb3beadcd57123` |
| `LogicLineages/PersistentMarking/NumberedWindowInternalLiteralTypeMembershipProof.lean` | `ab41683cc043a3b922c6f1c4a016bb95006fc40db488ca8b8e0faf84888a90b7` |
| `LogicLineages/PersistentMarking/NumberedWindowInternalGrammarCodomainProof.lean` | `db9cc902b8f7a0014726c083fb5e5552a377f09d394955537a9cb4cfbf1d970f` |

Both target hashes and the source-map hash match the pre-proof freeze. All four failed submitted drafts were preserved before their respective repairs: three SupportProof editions (gate04, gate06, gate07) and the initial main proof (gate08). No grammar proof repair was needed.

The five membership/transfer endpoints are supporting contracts for unconditional literal scratch-membership equivalence, finite actual-program guard/image transfer, and their original `TV`/refit instances. The two grammar endpoints derive the existing internal `GrammarCodomainInversion` from explicit finite numerical closure under the unchanged `cellTail`. This closes that internal grammar component under its stated finite premise. It does not supply closure for arbitrary settings, infer literal-window membership from arbitrary scalar acceptance, prove unrestricted all-type checker inversion, discharge every application guard, or promote a numbered Paper 16 theorem. The finite-refitted-checker obstruction #1475 remains unchanged.

The lane is complete and edits have stopped. Publication and evidence adoption remain with the root coordinator; no compiler or Git command was run by this lane.
