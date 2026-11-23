# Uniform conditional main theorem with an actual primitive-recursive tower code

Continuation date: 2026-11-22 (America/Chicago). The freeze record gives the
actual UTC timestamp separately. Source snapshot:
`b28541e6f1682fc41c47a385729df36e9db87b0d`, with the two new cooperating
packets described below.

## Printed scope

The principal theorem's final clause requires an effective family of closed
native T terms of outer type `o → o` whose ranks are cofinal in BH
(`16-persistent-marking-termination-ordering/paper.tex:108-113`). The printed
family is the sequence obtained by replacing the operations in (D) with their
native realizers (`sections/ordinals.tex:564-590`). Its literal syntax is
`NativeTowerSequenceTargets.sequenceTerm` (#1462).

The accepted `ConditionalHeightEffectiveTargets.EffectiveCofinalFamily`
(#1470) already retains exactly those syntax witnesses, their same-type native
ranks, strict cofinality, the bound on every family rank, and the fact that no
ordinary full rank equals BH. It does not assert `Primrec` of a natural-number
encoding. The new `ConditionalMain16UniformEffective` packet preserves all of
that while replacing the individual accessibility input of #1471 with the
uniform closed-theory input of #1472. Its target and source map have their own
earlier freeze.

## Actual code, not an additional hypothesis

The separate `NativeTowerCodeDefinitions/Targets/Proof` packet defines the
specific natural-number function `NativeTowerCode.sequenceCode`. Its targets
are an unconditional primitive-recursiveness theorem and calibration to the
literal ordinary translation/encoding of `sequenceTerm n`, hence to
`NativeSyntaxCountabilityTargets.nativeCode` of every closed native witness
with that syntax. The coding packet is owned and checked separately.

The new target imports the coding declarations only. Its proof will import
the coding theorems. Neither `Primrec sequenceCode` nor code calibration is
an input to the new conditional principal theorem.

## Frozen target and interpretation

New module:
`LogicLineages/NativeModule/PersistentMarking/ConditionalMain16UniformEffectiveCodedTargets.lean`.

The concrete family predicate `CodedEffectiveCofinalFamily BH` states:

1. `Primrec NativeTowerCode.sequenceCode`.
2. For every signature and actual full/native well-foundedness witnesses,
   there is a family `t : Nat → ClosedNativeTerm S indexType`.
3. Its syntax is `sequenceTerm n`, and its actual `nativeCode` is
   `NativeTowerCode.sequenceCode n`, for every `n`.
4. For every ordinal below BH, some member has a strictly larger native rank.
5. Every member's native rank is below BH, and no typed ordinary term's full
   confined rank equals BH.

The type `ClosedNativeTerm S indexType` retains closedness, native syntax,
ordinary source syntax, and the literal outer type `o → o`; the target does
not merely assert the existence of arbitrary codes with suitable ranks.
The full/native well-foundedness arguments are the same rank parameters used
by #1470. The main conclusion also retains `Items1to5`, which supplies full
confined well-foundedness, and the existing `HeightIsBH` statement. No new
well-foundedness hypothesis is introduced.

`Main16StatementCodedEffective BH` contains items 1-5, the ordinary-term upper
bound, height equality, and this coded family. Forgetting the code clauses
recovers the accepted `Main16StatementEffective BH`.

`ConditionalMain16UniformEffectiveCoded` has exactly the same five hypotheses
as the preceding uniform-effective packet: `NormTheorem BH`,
`UniformAccessibility`, `Calibration D`, `TowerHypotheses D`, and
`BHIdentification D BH`. The first two use derivability from the empty logical
assumption list, as established in `SOURCE-MAP.md`. The proof first obtains
the explicit family from the uniform-effective endpoint, then attaches the
unconditional code/calibration results to those same syntax witnesses.

## Limits and evidence plan

This is a supporting composition strengthening. It does not discharge any of
the five ordinal/accessibility hypotheses or promote a numbered statement.
It gives primitive-recursive generation of the actual syntax codes; it does
not claim that ranks, ordinal indices, or a choice of a cofinal witness from
an arbitrary ordinal input are computable.

Targets, this source map, and the coding declaration dependencies are hashed
before this packet's proof is written. `FROZEN-CODED.json` records those
hashes. The root owns the sole native/axiom gate; no proof-validity result is
claimed before that gate returns.
