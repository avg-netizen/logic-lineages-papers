# Paper 16 installed application: round-2 source and statement review

Review date: 22 November 2026 (America/Chicago).

Reviewed head: `1cd1734feb2b64c5a9936b2b5e8649f9b2f3889c`.

Comparison baseline: `a14a936772e01363795c919c106607fdad368f8c`.

Scope: the new application packets #1438, #1440 and #1442, their target propositions, relevant original program definitions and integration interfaces, round-2 source maps, evidence records, and handoff summary. All line references below identify the reviewed head, before review corrections.

## Result

No material mathematical or integration defect was found in the three packets. The actual target propositions retain the additional scalar type-checker premise where necessary, use matching operand reports at one shared context, and refer to the same installed least, scalar and application programs. Two low-severity documentation corrections remain.

This is a source/statement and integration-scope review. Native proof validity relies on the recorded successful gates listed below. No compiler run, duplicate native proof check, full manual proof-body acceptance review, Git operation, or change to the reviewed sources or their pins was performed for this review.

## Finding 1 — low severity: the summary omits the arbitrary scalar type-checker premise

Locations:

- `formalization/verification/local-fable-pair-2026-11-22-round2/HANDOFF.md:65` describes accepted output, actual application acceptance and output uniqueness as following from two accepted operand addresses, with the two original type guards retained.
- `formalization/verification/local-fable-pair-2026-11-22-round2/fable2/OUTPUT-ADDRESS-SOURCE-MAP.md:12` similarly summarizes the general `ExactInstalledApplicationOutputAddress` statement without its additional scalar result-type check.

The general targets also require an internal derivation of `unary tv (suc z) cod`:

- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationOutputAddressTargets.lean:41`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationFrontendAcceptanceTargets.lean:40`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationOutputFunctionalityTargets.lean:57`.

The operand reports must additionally specify a function result `rawCons dom cod` and an argument result `dom` at the same `ctx`; for example, see `NumberedWindowInternalCoverMeasuredApplicationOutputAddressTargets.lean:42` and `:43` in the same directory.

The additional check is substantive. Scalar acceptance of the operands supplies the arbitrary program `tv` at their result fields, `rawCons dom cod` and `dom`. Neither entails acceptance at `cod`. The original scalar definition explicitly checks its address's result field: `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalSparseCanonicalAddressTargets.lean:34` defines `shapeChecks`, and `:49` states the corresponding reported-address equivalence. Thus an accepted output reporting result type `cod` requires the scalar's own check at `cod`.

The `tv := TV` specializations correctly obtain this check from the second component of the retained syntax guard. They instantiate the installation with `TV`; they do not prove that an arbitrary source `tv` equals `TV`. The output-address source map already states the missing general premise accurately in its explicit-assumptions section at line 41 and explains this specialization boundary at line 55. The accepted Lean propositions require no correction.

### Corrected handoff wording

> Internal application on the installed carrier (#1438, #1440, #1442): for the installation with scalar type checker `tv := TV`, two accepted operand addresses with matching function/argument reports at one context and the retained syntax/refit type guards yield, under the object continuation, a measured least `m`, the accepted output address `addressTerm ctx cod m`, acceptance by the actual installed application program, and output functionality at that same address. For an arbitrary scalar type checker `tv`, the general statements additionally require `unary tv (suc z) cod`.

### Erratum for the frozen output-address source map

In the opening claimed-statement paragraph, replace the input summary with:

> Given the two original syntax/refit type guards, the additional result-type check `unary tv (suc z) cod`, the two matching operand address reports at one shared context `ctx`, and installed-scalar acceptance of both operand addresses, every goal follows that follows under the object continuation from the displayed three output facts. In the `tv := TV` specialization, the retained syntax guard supplies the additional result-type check.

This erratum belongs in the review record or a linked correction note. The previously frozen source map and its recorded hash should remain unchanged.

## Finding 2 — low severity: the functionality source map misstates the original guards' dependency

Location: `formalization/verification/local-fable-pair-2026-11-22-round2/fable2/OUTPUT-FUNCTIONALITY-SOURCE-MAP.md:65` says the original syntax/refit guards and the extra arbitrary-`tv` result check are consumed only by #1438's scalar-acceptance conjunct.

The original syntax/refit guards also support application-window formation and application least existence. Their explicit uses are visible at:

- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationOutputAddressProof.lean:71`, supplying the guards to wrapped auxiliary formation.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationOutputAddressProof.lean:75`, supplying them to installed-carrier application existence.

Only the additional arbitrary-`tv` result check is specific to the output scalar-acceptance step. The standalone held-least functionality proposition itself does not require either category of guard. Its least is already supplied as a premise.

### Corrected wording

> The original syntax/refit guards support application-window formation and least existence; the extra arbitrary-`tv` result check supports output scalar acceptance. The held-least functionality statement does not require these guards.

Record this as an erratum to the frozen map, without altering its pinned bytes. No target or proof correction is required.

## Confirmed target and integration scope

### One installed route throughout

`formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverCombinedMeasuredInstallDefinitions.lean:44` constructs the combined source and then installs its thin matching window, measured paired cover-guarded exchange, and packed least. At line 49 the scalar uses that same window and least; at line 58 the application is the original `applicationGuard I L`.

The original application frontend checks both scalar operands and then the physical application core. It does not insert a scalar check on its proposed output: see `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalSparseApplicationFrontendDefinitions.lean:43` and `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalSparseApplicationFrontendTargets.lean:67`. Consequently #1438's output scalar acceptance is an additional derived property, not a change to the application predicate that makes the desired conclusion automatic.

### #1438: accepted output address

`ExactInstalledApplicationOutputAddress` supplies the measured least of the actual `auxiliaryTerm dom cod fn arg`, the physical report of `addressTerm ctx cod m`, and scalar acceptance of that address, all on the same fresh witness under the continuation. See `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationOutputAddressTargets.lean:46`.

The output address stores the least `m` as its class field. It does not store the auxiliary term. The shared context check is obtained from operand scalar acceptance. The output window and the least fixed-point condition required for canonical scalar admission are derived. The general scalar result check remains an explicit premise; the `tv := TV` specialization discharges it from the retained syntax guard.

### #1440: actual frontend acceptance

The additional conclusion is `programGraph Q.application (suc z) ![qf, qa, addressTerm ctx cod m]`, with the appropriate relabeling under the continuation. See `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationFrontendAcceptanceTargets.lean:55`.

This is the graph of the actual installed application program. The original parsed-input requirements include physical address reports, arrow fields and shell equations; see `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalSparseApplicationFrontendTargets.lean:42`. The new theorem derives the additional parsing and row data from the supplied matching operand reports. It does not assume an application report, an arrow guard, shell equations, or an output block witness as additional hypotheses.

### #1442: output functionality

The standalone result holds the measured least call as a premise and concludes that any `y` accepted by the installed application on the reported operands equals `addressTerm ctx cod m`. See `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationOutputFunctionalityTargets.lean:29`.

The continuation form obtains its least and accepted output through #1440, retains the same assumptions, and supplies an internal implication for every term `y` in the extended context; see the same targets file at line 75. The field reports identify the context, type coordinates and operand class fields used by the original application row, so the comparison uses the same auxiliary term and least call. No operand-report uniqueness hypothesis or address-constructor injectivity hypothesis is introduced.

### Remaining boundaries

- The output witness remains under the object continuation; these packets do not package the result as a closed existential carrier-closure formula.
- Output functionality in the continuation is a schema over terms of the extended context, each yielding an internal implication. It is not one internally universally quantified formula.
- The standalone functionality theorem assumes the least call; the continuation version obtains it from the retained application-existence hypotheses.
- The two original syntax/refit type guards remain. The arbitrary-`tv` statements retain the separate result check.
- The `tv := TV` results choose that installation. They do not establish source calibration or identify an arbitrary original scalar type checker with `TV`.
- The results concern matching operand reports at one shared context. They do not establish functionality under replacing operands by equivalent addresses or application across different contexts.
- No numbered Paper 16 statement, full `InstalledTupleAt` calibration, or callback/base source correspondence is closed by these packets.

## Recorded native evidence

The reviewed evidence records report successful exact native gates and named-axiom output limited to `propext`, `Classical.choice` and `Quot.sound` for all seven exported endpoints:

| Packet | Exact receipt | Evidence record |
| --- | --- | --- |
| #1438, two endpoints | `1795397242217822492-3231382` | `formalization/verification/local-fable-pair-2026-11-22-round2/evidence/1438-p16-installed-application-output-address-native.json` |
| #1440, two endpoints | `1795397653724718198-3233856` | `formalization/verification/local-fable-pair-2026-11-22-round2/evidence/1440-p16-installed-application-frontend-acceptance-native.json` |
| #1442, three endpoints | `1795398283787789332-3247930` | `formalization/verification/local-fable-pair-2026-11-22-round2/evidence/1442-p16-installed-application-output-functionality-native.json` |

These existing gates establish proof validity. This review checks that the propositions and their source-facing descriptions express the intended conditional results; it does not repeat those gates or represent a fresh compiler validation.
