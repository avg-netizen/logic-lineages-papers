# Actual ordinal index tower: source map and preproof scope

Continuation date: 2026-11-22 (America/Chicago).
Base checkpoint: `9a8fd8f8ffd9c1ab27b91096dc1e52aa196bb413`.
The root approved this concrete supplier before target construction.

## Literal source

Paper 16 `16-persistent-marking-termination-ordering/sections/ordinals.tex:553-555`
sets Ω to the first uncountable ordinal, defines `a₀ = 0` and
`aₙ₊₁ = Ω^(aₙ)`, and uses `Λ = supₙ aₙ`. The initial values are consequently
`0, 1, Ω`; starting at Ω would shift the displayed sequence and is not this
packet's definition.

The existing `ConditionalTowerCofinality.TowerHypotheses` asks for strict
increase, each argument below its endpoint, and strict cofinality at
`LogicLineages/PersistentMarking/ConditionalTowerCofinalityTargets.lean:38-46`.
Those fields have so far been assumed for abstract index data. This packet
proves their actual ordinal instances, together with the endpoint's least
fixed-point property. It does not repackage `TowerHypotheses` as a premise.

## Concrete definitions

`LogicLineages/PersistentMarking/ActualOmegaTowerDefinitions.lean` defines:

```text
omegaIndex : Ordinal.{0} := ω₁
powerStep a := omegaIndex ^ a
argument n := powerStep^[n] 0
endpoint := sup_n argument n
```

`Ordinal.omega 1`, written `ω₁`, is Mathlib's first uncountable ordinal
(`Mathlib/SetTheory/Cardinal/Aleph.lean:199-212`). These are actual ordinals
in the full index order, not elements of the countable-ordinal value type
used for realization. The supremum is the ordinal supremum of the literal
sequence. No order, normality, or cofinality property is an input.

## Frozen targets

`ActualOmegaTowerTargets.lean` freezes seven unconditional propositions:

1. `LiteralRecurrence`: the actual Ω identity, the initial values 0, 1, Ω,
   and the exact power recurrence.
2. `StrictlyIncreasing`: `StrictMono argument`.
3. `BelowEndpoint`: every finite argument is strictly below its supremum.
4. `Cofinal`: an ordinal is below the endpoint exactly when it is strictly
   below some argument.
5. `EndpointAsNfp`: the supremum equals the least fixed-point construction
   `Ordinal.nfp powerStep 0`.
6. `EndpointFixedPoint`: `Ω^endpoint = endpoint`.
7. `EndpointLeast`: every pre-fixed point `Ω^a ≤ a` bounds the endpoint.

`FullActualOmegaTower` conjoins these exact propositions. The planned proof
module is `LogicLineages/PersistentMarking/ActualOmegaTowerProof.lean` in the
same namespace. Its public aliases are `exact_` followed by each target name.

The proof uses actual ordinal arithmetic: `1 < ω₁` gives normality of
`Ω^·`; strict monotonicity propagates `0 < Ω^0`; the supremum of finite
iterates is `nfp`; normality and the minimality theorem supply fixedness and
the least pre-fixed-point bound. Relevant pinned Mathlib declarations are
`isNormal_opow` (`Ordinal/Exponential.lean:116-120`),
`iSup_iterate_eq_nfp`, `lt_nfp_iff`, `iterate_lt_nfp`, `nfp_fp`, and
`nfp_le_fp` (`Ordinal/FixedPoint.lean:252-314`).

## Remaining actual ordinal construction

The manuscript also identifies this supremum with `ε_(Ω+1)`. This packet
does not define epsilon notation to be the supremum. A separate literal
Mathlib epsilon bridge must establish that identity. Mathlib's epsilon
function is `Ordinal.veblen 1`, with `epsilon_succ_eq_nfp` in
`Ordinal/Veblen.lean:543-575`; connecting its index Ω to Ω itself requires
additional ordinal facts and is a distinct target.

The coefficient norm is likewise not defined as the constant one to obtain
`normBound`. A concrete hereditary Ω-normal-form/coefficient interpretation
is needed before the paper's bound on `|aₙ|` can be discharged. A subsequent
collapse construction must use the intended Veblen-hull criticality and
coefficient norm, prove existence/minimality of its values, and connect it
to the cited calibration. Neither ψ nor BH is defined in this packet.

Thus the result discharges the actual index-order portion of the current
interface unconditionally. It does not establish `TowerHypotheses` in full,
Simmons calibration, BH identification, the ID1 norm theorem, or internal
accessibility. It is supporting progress, not a numbered promotion.

## Freeze and gate

Definitions, targets, and this source map are written before any proof.
`FROZEN-OMEGA-TOWER.json` records their hashes, the exact manuscript hash,
and the pinned Mathlib source hashes. The root owns the sole native compiler
and acceptance queue. Existing source, frozen targets, pins, and failed
drafts are preserved.
