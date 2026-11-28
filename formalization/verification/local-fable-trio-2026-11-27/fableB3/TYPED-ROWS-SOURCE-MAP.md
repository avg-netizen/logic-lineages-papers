# Source map for the targets frozen by Fable B3 (27 November 2026)

All three Targets modules serve Paper 16 `lem:arithmetic-accessibility`
(`16-persistent-marking-termination-ordering/sections/ordinals.tex`, line 79 and its proof) and
checkpoint 4 of `verification/paper16-remaining-targets-2026-11-25/TARGETS.md`, "Internal
accessibility" ("Close `TypedCarrierComputability` by the manuscript's neutral, lambda,
constructor, and structural inductions"). Each module's docstring states what is assumed and
what is not claimed; this file only indexes them against the printed proof and the map
(`TYPED-COMPUTABILITY-MAP.md`).

| Targets module (`LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestone…`) | Statements | Printed sentence | Map rows |
| --- | --- | --- | --- |
| `TypedRowsTargetsV2` | `WindowNeutralFacts` | "a non-lambda is computable whenever all its direct reducts are computable; variables and bottoms are computable" | N1–N3 |
| | `WindowBetaApplication` | "The direct reducts of (λx.V)U are its given beta instance, a function-side body reduct, or bottom … The neutral argument gives the application" | B1, B2 |
| | `LambdaFactFromReducts` (with `LambdaReducts`, `LambdaFact`, `InstancesComputable`) | "The lambda fact … and hence the lambda" | B7 reduced to B5/B6/B8 |
| | `TypedComputabilityFromRows` (with open rows `NeutralReducts`, `GroundNotLambda`, `LambdaReducts`, `LambdaInstances`) | "Structural induction under a computable substitution now makes every auxiliary term computable" — the split of that claim by the neutral lemma and the lambda fact; the induction itself is inside the open rows | assembly, §2 |
| `GeneralSeedLeastTargetsV2` | `GeneralSeedLeast`, `GeneralSeedLeastOnJoinedWindow` | "Function-side closure gives downward closure of (T)" — the totality half: the application of an admitted function to an admitted argument exists | N7, D3 |
| `ApplicationResultTargetsV2` | `ApplicationResultTyped` | typing of `QU` at the codomain ((T), "quantification over computable typed arguments") | B3, D4 |

Common assumptions: an `InstalledWindow` with the `BetaJoinedRulesAt` package at its own
programs (`JoinedAt`), and where stated the guard equation, `CarrierTypingCases`, or the
scalar/least equations with `MemoSelectedReports` and `OpenRankTypeGuards`. All of these are
exported by `Paper16AccessibilityMilestoneFreshCarrierTargetsV2.FrontLiteralWindowTyping`
(proved, receipt `1795815925311427086-1102198`). None of the targets asserts
`TypedCarrierComputability`, `AllTerms` or the lemma.
