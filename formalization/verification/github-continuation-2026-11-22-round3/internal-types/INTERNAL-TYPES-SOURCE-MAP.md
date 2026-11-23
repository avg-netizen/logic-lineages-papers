# Internal finite type membership and grammar codomain inversion

Base: `9a8fd8f8ffd9c1ab27b91096dc1e52aa196bb413`. User continuation released on 22 November 2026 (America/Chicago). This source map and both target modules are frozen before proof authoring; UTC freeze hashes appear in `LEDGER.md`.

## Missing component and approved scope

The actual all-type checker is supplied existentially through the original primitive-recursive correspondence (`NumberedWindowAddressProgramProof.typeProgram` and `NumberedWindowInternalSparseAddressPositiveNumericChecks.exact_ConcreteAddressPositive`). Its `ActualTypeGuard` calibration concerns numeric evaluation. No accepted internal unfolding law for an arbitrary such witness gives unrestricted open-term arrow inversion.

The G05 source map for #1461 identified a finite internal route for the original grammar-membership component: eliminate membership in a literal finite list, identify a branch with a numeral, and build the corresponding original program proof. The new packet constructs this route rather than assuming an internal calibration/inversion rule. It preserves the exact original `scratchMember`, `cellTail`, supplied `TV`, and supplied `T` programs.

The finite-refit obstruction #1475 remains intact. This packet does not install the refitted checker in the actual all-type slot. It gives derivations from explicit finite-list membership and finite numeric facts about the unchanged programs.

## Frozen statements

`LogicLineages/PersistentMarking/NumberedWindowInternalLiteralTypeMembershipTargets.lean` defines:

- `literalMembership codes x`: `memberGraph (numeral (Encodable.encode codes)) x`, the original standard scratch-list membership graph at an arbitrary open candidate.
- `literalChoices codes x`: the actual finite disjunction of `x = numeral code`, ending in falsity. No default candidate is added for an empty list.
- `ExactLiteralTypeMembership`: both implications between those two formulas, derivable for every body, ordinary context, finite numeric list and open candidate, without premises.
- `ExactFiniteProgramGuardTransfer`: if the original program `p` evaluates to one at every listed numeral, literal membership of an open candidate yields its actual unit `p` graph internally.
- `ExactFiniteProgramImageTransfer`: if every listed input's actual `p` value lies in an output list, literal input membership and the actual open `p` graph yield literal output membership.
- `ExactFiniteActualTypeGuard`: instantiate finite guard transfer at the original supplied `TV`, assuming `ActualTypeGuard TV` and validity of every numeral in the finite list.
- `ExactFiniteWindowRefitGuard`: instantiate it at the existing `refitGuard s T`, assuming `TypeGuardCalibrated s T`, `GrammarTypeInclusion s`, validity of each window-list entry, and actual internal membership in the literal window list.

`LogicLineages/PersistentMarking/NumberedWindowInternalGrammarCodomainTargets.lean` defines:

- `FiniteCodomainClosure codes`: for every `code` in the literal list, `evaluate cellTail [code]` belongs to that list. This is an explicit finite numerical property of the original sparse-cell tail program. It is not assumed for arbitrary settings.
- `ExactOpenFiniteGrammarCodomain`: under that finite closure for `s.types`, the original calculus derives the implication from literal grammar membership of `rawCons dom cod` to literal grammar membership of the open `cod`.
- `ExactFiniteGrammarCodomainInversion`: the existing `GrammarCodomainInversion body s` predicate from #1461 follows from that same finite numeric closure, with no internal-law premise.

All contexts and open term arguments remain the actual ones. No source program, scalar, window or application predicate is modified.

## Dependencies and construction

Paths here are relative to `formalization/`.

- `LogicLineages/PersistentMarking/NumberedWindowInternalSparseScratchMembershipDefinitions.lean`: unchanged `memberBase`, `headMatches`, `memberStep`, `scratchMember`. This program consumes the standard scratch-list encoding, not the separate sparse polynomial encoding used for type arrows.
- `LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/InternalRawListRecursionProof.lean`: genuine nil and cons equations, `nilRecover`, `consForward`, and `stepCases` expose the original recursive call on the same tail.
- `LogicLineages/PersistentMarking/NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof.lean`: original head/tail membership introductions.
- `LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/InternalEqualityTestProof.lean`, the branch and graph support proofs: actual head comparison, branch recovery, graph functionality and equality transport.
- `LogicLineages/PersistentMarking/NumberedWindowNumeralGraphChecks.lean`: `exact_NumeralGraph` constructs an original-calculus proof for the actual supplied program at each concrete numeral tuple. It is used only after a finite list case identifies the input with one listed numeral.
- `LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/InternalListCodecEvaluationProof.lean`: the standard cons program evaluates to the original list encoder, identifying the literal cons cells used in finite-list induction.
- `LogicLineages/PersistentMarking/NumberedWindowInternalSettingsGrammarGuardNumericProof.lean`: existing calibration of the original refit program under its existing grammar-inclusion and guard-calibration premises.
- `LogicLineages/PersistentMarking/NumberedWindowInternalSparsePathEnvelopeOpenCellProof.lean`: `canonicalCell` gives the actual `cellTail` graph with output `cod` on `rawCons dom cod`, at arbitrary open fields. The finite image-transfer theorem then yields the codomain's literal grammar membership.

The key distinction is finiteness: numeric evidence is converted into a finite collection of concrete numeral proof trees, and internal equality transports those proofs in each branch of an internally established finite disjunction. There is no inference from arbitrary numeric correctness to a rule at an unrestricted open input.

## Premises and boundaries

- Literal membership equivalence is unconditional. Finite guard/image transfer states every pointwise finite numerical premise explicitly.
- The actual-type instance retains the real `ActualTypeGuard` calibration and finite entry validity. The refit instance retains the real `TypeGuardCalibrated`, grammar inclusion and finite window validity premises.
- Internal membership in the literal window list is explicit. No claim says an arbitrary accepted installed scalar or matching window already gives that membership.
- The grammar codomain result retains `FiniteCodomainClosure s.types`; no closure is inferred from the bare `Settings` structure. This condition covers every listed code's actual numeric `cellTail` output, and the packet does not silently replace it by a weaker condition applying only to selected valid arrows.
- Unrestricted `ArrowCodomainInversion body TV` for the actual all-type checker remains open. No arbitrary source calibration is reflected into the calculus, and no `SyntaxGuardRefits` rule is used.
- The result does not discharge all application guards, build a refitted `InstalledTupleAt`, establish internal accessibility, or promote a numbered Paper 16 theorem.

## Freeze status

Targets and this map precede proof authoring. Root owns the sole exact fixed-limit native/axiom gate. Native status is pending at freeze time; failed drafts will be retained before repairs. Existing accepted sources, frozen maps, hashes, compiler policy and Git state are outside this lane's editing scope.
