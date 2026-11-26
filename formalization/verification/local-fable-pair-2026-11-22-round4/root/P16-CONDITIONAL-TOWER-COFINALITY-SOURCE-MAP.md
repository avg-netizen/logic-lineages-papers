# Paper 16 `lem:tower-cofinality`, conditional on its cited inputs

Printed lemma (`sections/ordinals.tex`): sup_n ψ_B(a_n) = ψ_B(Λ) = BH. Its proof uses the
characterization (P) of ψ_B cited from Simmons 2004 §5, the coefficient-norm bound |a_n| ≤ 1, the two
increasing cofinal sequences, closure of the N_B-critical ordinals under increasing countable suprema,
and, for the last equality, the identification ψ_B(ε_{Ω+1}) = BH cited from Pohlers §§9.4–9.5. None of
ψ_B, the norm, criticality or BH has a definition in the repository.

Frozen `LogicLineages/PersistentMarking/ConditionalTowerCofinalityTargets.lean`
(sha256 `3d850d603dfe1018ae254f853de31b3978445f60a88666f9cccac9ad79014fa7`), over ABSTRACT data
`CollapseData I O` (two linear orders, `psi`, `norm`, `critical`, `one`, `endpoint`, `a`):
- `CharacterizationP` — (P) as printed: `psi ξ` is the least critical θ with η < ξ ∧ |η| < θ → psi η < θ.
- `TowerHypotheses` — (P); a increasing, below and cofinal in the endpoint; |a_n| ≤ one; critical values
  exceed one; a least upper bound of a strictly increasing sequence of critical values is critical.
- `ConditionalTowerIncreasing` — the collapse values along the tower strictly increase.
- `ConditionalTowerSupremum` — any least upper bound of them equals `psi endpoint`.
- `ConditionalTowerCofinality` — with `psi endpoint = BH` as one more hypothesis, it also equals BH.

Proof: the printed argument, line for line; pure order reasoning. Receipt `1795403715284492323-3286409`.

Two readings made explicit, for a reviewer: "1 < ψ_B(a_m)" and "1 < ψ_B(Λ)" are obtained from
"critical values exceed one" (the printed proof uses them without comment); and the supremum is taken as
any least upper bound, so no completeness of the value order is assumed.

This is a supporting statement. It does not promote the numbered lemma: every hypothesis is an
uninstantiated assumption about objects the repository does not define.
