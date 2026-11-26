# Closed-theory ordinal interface and uniform effective main theorem

Source snapshot: `b28541e6f1682fc41c47a385729df36e9db87b0d`.
Review and target freeze date: 2026-11-23.

## Assumption-context review

The suspected arbitrary-assumption-context defect is absent from the accepted
interfaces. `ExternalOrdinalInterfaceID1Targets.lean:28-31` requires
`Nonempty (Derivation B [] I(n))` in `NormTheorem`. Its
`InternalAccessibility` definition at lines 35-36 also requires a derivation
from `[]`. `InternalCalculusDefinitions.lean:79-82` confirms that this list is
the actual logical assumption context. `SourcePresentationDefinitions.lean:34-41`
uses the separate natural-number argument `context` to specialize the source
presentation, and `allTermsFormula` is a closed formula over `Empty`.

`ConditionalUpperTargets.IndividualAccessibility` retains `[]` in each
individual atom. `ConditionalUpperUniformTargets.UniformAccessibility`
requires a closed proof of the all-terms sentence for checker programs
evaluating the window's original four checks. The numeric existential context
cannot make the scalar domain empty by fiat: `NumberedWindowCheckerCoordinates.domain`
ignores that coordinate, and `Evaluates` fixes the scalar test at every address
(`NumberedWindowCheckerCoordinates.lean:8-19`,
`NumberedWindowFormulaCalibrationTargets.lean:13-17`). The bridge proves the
carrier formula internally at each admitted numeral and keeps the empty
assumption list (`ConditionalUpperUniformBridgeProof.lean:49-69`).

This matches the source norm input at
`16-persistent-marking-termination-ordering/sections/ordinals.tex:307-313`:
individual membership provable in ID1, rather than membership derivable from
arbitrary assumptions. An arbitrary-assumption generalization would admit
`I(n)` by the hypothesis rule even for an empty inductive operator, but no
accepted target makes that generalization. No counterexample to the current
closed-theory interface is claimed.

## Concrete composition gap

`ConditionalUpperUniformTargets.ConditionalMain16Uniform` (#1473, lines 72-76)
concludes `ConditionalMain16Targets.Main16Statement`. Its definition at
`ConditionalMain16Targets.lean:37-38` contains items 1-5, the upper bound, and
height equality. It does not contain the explicit cofinal sequence.

The preceding #1471 concludes
`ConditionalMain16EffectiveTargets.Main16StatementEffective` (lines 18-25),
which strengthens height equality with `EffectiveCofinalFamily` through
`ConditionalHeightEffectiveTargets.HeightIsBHEffective` (lines 27-37).
The printed principal theorem explicitly requires an effective cofinal family
of closed native terms of outer type `o → o`
(`16-persistent-marking-termination-ordering/paper.tex:108-113`).

The accepted #1473 is valid for its stated weaker conclusion. The gap is that
the uniform hypothesis and explicit family are not retained together in that
published endpoint.

## Frozen new target

New module:
`LogicLineages/NativeModule/PersistentMarking/ConditionalMain16UniformEffectiveTargets.lean`.

Frozen proposition:
`ConditionalMain16UniformEffectiveTargets.ConditionalMain16UniformEffective`.

For every abstract index order, collapse data, and ordinal `BH`, its hypotheses
are exactly:

1. `ExternalOrdinalInterfaceID1Targets.NormTheorem BH`.
2. `ConditionalUpperUniformTargets.UniformAccessibility`.
3. `ExternalOrdinalInterfaceTargets.Calibration D`.
4. `ConditionalTowerCofinality.TowerHypotheses D`.
5. `ExternalOrdinalInterfaceTargets.BHIdentification D BH`.

Its conclusion is the unchanged accepted `Main16StatementEffective BH`.
The proof composes `ConditionalMain16EffectiveProof.exact_ConditionalMain16Effective`
(#1471) with `ConditionalUpperUniformProof.individualOfUniform` (#1472).
It adds no hypothesis and changes neither the original source semantics nor
any accepted/frozen target.

## Boundaries

This is a supporting conditional assembly. It does not prove the norm theorem,
uniform internal accessibility, Simmons calibration, collapse facts, or the
identification with BH. It does not promote a numbered statement. The existing
`EffectiveCofinalFamily` identifies the witnesses with the explicit recursive
`sequenceTerm`; a subsequent, separately frozen target will attach a proved
primitive-recursive natural-number code for that actual sequence. No abstract
or assumed coding supplier is added here.

Native compilation and axiom checks belong to the root's serialized queue.
Targets and this source map are hashed before the proof file is created;
the hashes are recorded in `FROZEN-UNIFORM-EFFECTIVE.json`.
