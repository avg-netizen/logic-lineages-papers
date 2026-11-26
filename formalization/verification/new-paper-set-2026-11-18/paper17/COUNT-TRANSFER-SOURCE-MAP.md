# Current17 `lem:count-transfer`: source map of the frozen target

Target: `LogicLineages.PermittedControl.Targets.FullCountTransfer` (`CountTransferTargets.lean`). Frozen
before proof in `COUNT-TRANSFER-FREEZE.json`. Written by the local Claude root on 21 November 2026. **No
independent pre-scope review was run**; this map is the author's own correspondence argument.

## Printed statement

`arithmetic.tex` 95–162. A count occurrence τ_P(x) of a proper interval P = (λ, μ) that is not short is
annotated by its full value C_P(x) = f(E_{P'}(x)), its prefix P' = (λ, η) with η = μ + ω² (identity
convention if λ = η) and the constant κ_μ = 1 − ⌈N(μ)/2⌉, through equation (count-core). The lemma: a class
with zero combined leading coefficient can be replaced exactly by its prefix counts and constants;
equal-input prefixes merge; prefixes on distinct inputs can be transferred to smaller input ranks whenever
their cores coincide.

## Clause by clause

| Paper | Formal clause |
|---|---|
| Equation (count-core): τ_P(x) = ½C_P(x) + τ_{P'}(x) + κ_μ | `CountCore`: for both selected controls, every λ < ε₀ limit, μ zero or limit, μ < λ, not λ = μ + ωk, and x ≥ max(N(λ), N(μ)+3): η ≤ λ, and there are actual first entries of the descent from λ + (x − N(λ)) into [η, η+ω) with count i and into [μ, μ+ω) with count k, with E_{P'}(x) = f^i(x) and 2k = f(E_{P'}(x)) + 2i + 2κ_μ. For λ = η the first entry is the start itself (i = 0, E = x): the identity convention |
| Equation (zero-replacement): bC + Σ aᵢ τ_{Pᵢ}(xᵢ) = Σ aᵢ τ_{Pᵢ'}(xᵢ) + Σ aᵢ κᵢ when 2b + Σ aᵢ = 0 | `ZeroClassExact`: for any finite family of such intervals and inputs, integer coefficients a, b, a common full value C = f(E_{P_s'}(x_s)), and any actual counts k_s and prefix counts i_s |
| Same input, equal cores: entry norms f^r(x) = f^s(x) give r = s, so the counts merge | `EqualInputMerge`: two proper intervals at one input x ≥ max(2, N(λ), N(μ)) (both intervals) with equal actual entry norms have equal actual counts |
| "Input comparison forbids δ_{P'} ≥ δ_{Q'}" for x < y with E_{P'}(y) = E_{Q'}(x) | `DistinctInputGap`: on the explicit gap-input tail, equality of the entry norms of (λ, μ) at y and (λ', μ') at x < y gives λ − μ < λ' − μ' |
| The collision table forces the equality certificate, y = E_H(x) with H = (λ_{Q'}, μ_{Q'} + δ_{P'}), and equation (rank-transfer) τ_{P'}(y) = τ_{Q'}(x) − τ_H(x) | `RankTransfer`: Q' = (λ, μ) at x, P' = (ν + δ, ν) at y, δ a limit with δ < λ − μ, both inputs on the effective inverse-table tail of accepted supporting work. If the actual entry norms coincide then there is an actual first entry of Q's descent into [μ+δ, μ+δ+ω) with count i and norm exactly y, and τ_{Q'}(x) = i + τ_{P'}(y) |

Every count and entry norm is the actual first-hit count and norm of the actual descent
(`FirstEntry`, `entryNormAt`, `countInitial`), for the factorial control and every near control
(`SelectedWithThreshold`). No entry, funnel hit, certificate sign or collision is a hypothesis except the
two entries whose counts are being related.

## What the target does not contain

- "Identity and short prefixes become constants": the identity case is inside `CountCore`; the constant
  count k of a short interval is the accepted `prop:entry-residues` and is not restated.
- "Choose the smallest surviving input and transfer every higher one to it": the iteration over a class is
  bookkeeping on top of `RankTransfer`; its charge is `lem:inner-termination` (record 702). The two records
  are not linked by a formal statement that the abstract replacement of 702 is the one justified here.
- The bounds (core-error), the annotation discipline, pattern guards, and the claim that every remaining
  prefix is proper after the removals are surrounding text, not part of the lemma.
- `RankTransfer` takes P' in the form (ν + δ, ν) with δ a normal-form gap, which is how the accepted
  inverse table is stated; a proper interval (λ', μ') is of this form with δ = λ' − μ'.
- Tails are explicit and effective but are not claimed minimal.

## Proof route (for orientation only)

`CountCore`: decompose μ = P + ωj with ω² | P, so η = P + ω²; long intervals have η ≤ λ. If η < λ the
accepted affordable cocycle splits the count at the first entry into η; one exact funnel passage (the
funnel branch of the long-entry residue proof, with the count kept) gives the remaining count
(f(q) − N(P))/2 − j + 1. `ZeroClassExact` is linear algebra over `CountCore` and uniqueness of first
entries. `EqualInputMerge` uses the entry orbit E = f^τ(x) and strict increase of iterates. `DistinctInputGap`
is the contrapositive of the accepted gap-input comparison. `RankTransfer` reads the accepted inverse
table: equal values exclude the two strict certificate signs, the equality row gives y = E_H(x), and the
cocycle continuation from y has the same terminal norm as P', hence the same count.
