# Paper08 uniform kernel separation: exact source correspondence

## Source and baseline

The baseline is `e5c70ae3` on
`formalization/cumulative-continuation-2026-11-04-second`. Its finite-source
comparison theorem remains accepted and its proof files are unchanged.

The target is paper08 `lem:uniform`, beginning at line 338 of
`08-multivariate-collapse-comparison/paper.tex`. The manuscript and the existing
`UniformCompletion/Definitions.lean`, `Targets.lean`, and `TargetChecks.lean`
are preserved byte for byte. Their hashes are recorded in `FROZEN-TARGETS.json`.

The interrupted conversation supplied a progress report but no proof files or
native receipts in this workspace. This continuation reconstructs the missing
proof and records its own native verification. The earlier reported success
is not used as acceptance evidence.

## Literal semantics and domain

The control is the existing `Phi`. The source budget at step `i` is
`(Phi^[i+1]) t - c`; the initial ordinal is `omega^d`. `sourceCount` is the
first-finite count of this independently scheduled, limit-part predecessor
process, and `sourceValue` iterates the original control by that count.
`sourceSignedDepth` adds the signed integer offset to the count. Its raw value
uses `Int.toNat`; the full theorem separately proves the signed depths are at
least `Phi t`, so this totalization never supplies an invalid positive-depth
claim.

This is the corrected source convention already adopted on 4 November. The
historical whole-current-state discrepancy and its counterexamples remain
unchanged. No further manuscript correction or semantic replacement is made.

The numerical region is exactly

```
3 <= d
degreeThreshold d <= t
degreeConstant d * (c + e + j.natAbs + k.natAbs + R + 1) <= Phi t
```

Here `degreeConstant d = 1000*d*d`, `degreeThreshold 3 = 16`, and for
`d >= 4`, the threshold is `max (degreeThreshold (d-1))
(100*degreeConstant (d-1)+100*d)`. The natural masses `c,e`, natural allowance
`R`, and signed offsets `j,k` retain their full domains. In particular, there
is no added requirement that `c+d+1 <= t` or `e+d+1 <= t`.

## Clause correspondence

| Source clause | Unchanged frozen target | Proof |
|---|---|---|
| Defined signed depths at least `Phi t`, with corresponding output lower bounds | `UniformDepthAndOutputBounds` | `Focused.uniformDepthAndOutputBounds` |
| `Phi^[R] (X^d_{e,k}(t)) < X^d_{c,j}(t+1)` | First conjunct of `QuantitativeSeparation` | `Proof.quantitativeSeparation` |
| If `c<e`, `Phi^[R] (X^d_{e,k}(t)) < X^d_{c,j}(t)` | Second conjunct of `QuantitativeSeparation` | `Proof.quantitativeSeparation` |
| Exact signed-index order at equal mass and input | `ExactSignedOrder` | `Focused.exactSignedOrder` |
| Equality exactly when input, mass, and signed offset coincide on a computed common tail | `EffectiveEqualityTail` | `Proof.effectiveEqualityTail` |
| Effective numerical constants and common-tail construction | `UniformTailPrograms` | `Focused.uniformTailPrograms` |
| Entire source lemma | `FullUniformSource` | `Proof.fullUniformSource` |

The independent expanded comparator remains `TargetChecks.lean`. The new
`QuantitativeTargetChecks.lean` expands each intermediate supplier statement;
it does not redefine the source goal. Its native preflight precedes native
checking of the new proof closure.

## Quantitative argument

### Budget comparison and exact blocks

The stronger shifted-budget comparison permits an adverse retained mass up to
the previous first budget, `a <= Phi t`. The successor growth of `Phi` pays
this mass uniformly at every subsequent scheduled step. Actual scheduled
count monotonicity therefore gives count order between inputs `t` and `t+1`,
and their different seeds give strict value order.

The broad source block identity is obtained from the existing exact ordinal
block cut. Its child is evaluated at
`K = sourceValue d (c+d) t`, where the cut proves `c+d <= K`. This is exactly
the genuine-input bound needed to identify the lower-rank companion with the
independent source process. No such identification is made at an invalid
original input. The helper also retains the complete additive count identity.

### Cubic case

At genuine quadratic child inputs, the count is
`Phi w/2 - (c+1)/2 + 1`. For adjacent cubic masses, either their quadratic
ceilings differ immediately or they differ after both masses are shifted by
three. The first case is strict after one aligned block; the second is strict
after two. A third aligned quadratic block amplifies the resulting integer
input gap to the requested `R` control iterations. The shifted-budget count
comparison supplies the corresponding cross-input gap.

This establishes the frozen cubic statement under
`16 <= t` and `9000*(c+e+R+1) <= Phi t`. The proof needs only part of this
available margin; it neither changes the constants nor adds a residue premise.

### Higher ranks and signed offsets

One exact block decomposition reduces rank `d+1` to rank `d`. The smaller
child input is at least `Phi t`, and monotonicity of the original constants
and thresholds establishes the lower-rank region there. The child masses
remain `c,e`. At the same input, weak order of the inner values suffices;
at adjacent inputs, shifted-budget order makes the inner inequality strict.

For signed offsets, the unsigned allowance is exactly
`R+j.natAbs+k.natAbs`. Adding the outer `+1` gives precisely the original
regional budget. Applying `Phi` forward by `j.natAbs` absorbs a negative
left offset and a positive right offset. Strict monotonicity then cancels
those common iterations. No inverse control or extra allowance is assumed.

### Equality on the computed tail

The original `equalityTail` is unchanged, including its cross-pair and both
self-pair budget bounds. Its cross-pair bound pays the region at every later
input. Signed values at fixed mass and offset are monotone in their input,
because the actual scheduled counts and their integer depths are monotone.
Adjacent quantitative separation consequently excludes equality at any two
different inputs. Same-input separation excludes distinct masses; exact signed
order then excludes distinct signed offsets. Domain and positive-depth
conclusions are derived in the same theorem. The existing primitive-recursive
tail proof supplies effectivity.

## Focused supplier provenance

All focused supplier files are new and namespace-isolated under
`UniformCompletion.Focused`. Their frozen aliases retain the original complete
target types. Each file records the original proof blocks from which it was
extracted. The source input, process bridge, calibration, ordinal block cut,
scheduled order, depth bounds, and elementary order/effectivity proofs keep
their existing mathematical obligations.

The elementary control growth estimate is extracted from
`CounterLeaderBoundsGrowthProof`. The direct power-of-two and parity argument
comes from `CounterLeaderExpansionSuppliersProof`. They avoid importing the
unneeded general residue/totient development. The memory, CPU, wall, worker,
and free-memory limits of the shared checker are unchanged.

## Acceptance boundary

Native acceptance is recorded separately in `ACCEPTANCE.json` and
`NATIVE-VERIFICATION.json`. Only `08-multivariate-collapse-comparison:lem:uniform`
is eligible for a status change from this component. Full first-order BASE,
the polynomial-head comparison chain, and every other pending source statement
remain separate obligations. This focused check makes no full-root or remote-CI
claim.
