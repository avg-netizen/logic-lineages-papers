module

public import Mathlib.SetTheory.Ordinal.Rank

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalTowerCofinality

universe u v

/-- Abstract data of the collapse used in Paper 16 `lem:tower-cofinality`:
an index order (the paper's uncountable arguments), a value order (the
countable ordinals), the collapse `psi`, the coefficient norm, the class of
`N_B`-critical values, the value `one`, the endpoint `Λ` and the tower
arguments `a_n`. Nothing here is defined concretely. -/
structure CollapseData (I : Type u) (O : Type v) where
  psi : I → O
  norm : I → O
  critical : O → Prop
  one : O
  endpoint : I
  a : ℕ → I

variable {I : Type u} {O : Type v} [LinearOrder I] [LinearOrder O]

/-- The characterization (P) cited from Simmons 2004, Section 5: `psi ξ` is
the least critical `θ` such that `η < ξ` and `|η| < θ` imply `psi η < θ`. -/
def CharacterizationP (D : CollapseData I O) : Prop :=
  ∀ ξ : I, D.critical (D.psi ξ) ∧
    (∀ η, η < ξ → D.norm η < D.psi ξ → D.psi η < D.psi ξ) ∧
    ∀ θ, D.critical θ → (∀ η, η < ξ → D.norm η < θ → D.psi η < θ) → D.psi ξ ≤ θ

/-- Everything the printed proof of `lem:tower-cofinality` uses besides
order reasoning: (P); the tower arguments increase, lie below the endpoint
and are cofinal in it; `|a_n| ≤ 1`; critical values exceed one; and a least
upper bound of a strictly increasing sequence of critical values is
critical ("the countable supremum is therefore an N_B-critical ordinal"). -/
structure TowerHypotheses (D : CollapseData I O) : Prop where
  characterization : CharacterizationP D
  increasing : ∀ n, D.a n < D.a (n + 1)
  below : ∀ n, D.a n < D.endpoint
  cofinal : ∀ η, η < D.endpoint → ∃ n, η < D.a n
  normBound : ∀ n, D.norm (D.a n) ≤ D.one
  criticalAboveOne : ∀ θ, D.critical θ → D.one < θ
  criticalSup : ∀ f : ℕ → O, StrictMono f → (∀ n, D.critical (f n)) →
    ∀ θ, IsLUB (Set.range f) θ → D.critical θ

/-- `lem:tower-cofinality`, first equality, conditional on the cited
inputs: the supremum of the collapse values along the tower is the collapse
at the endpoint. The supremum is any least upper bound. -/
def ConditionalTowerSupremum : Prop :=
  ∀ (I : Type u) (O : Type v) [LinearOrder I] [LinearOrder O] (D : CollapseData I O),
    TowerHypotheses D →
    ∀ θ, IsLUB (Set.range (fun n => D.psi (D.a n))) θ → θ = D.psi D.endpoint

/-- The collapse values along the tower are strictly increasing (the
first step of the printed proof). -/
def ConditionalTowerIncreasing : Prop :=
  ∀ (I : Type u) (O : Type v) [LinearOrder I] [LinearOrder O] (D : CollapseData I O),
    TowerHypotheses D → StrictMono (fun n => D.psi (D.a n))

/-- The full printed lemma: with the cited identification of the endpoint
value with `BH` (Pohlers, Sections 9.4–9.5) as one more hypothesis. -/
def ConditionalTowerCofinality : Prop :=
  ∀ (I : Type u) (O : Type v) [LinearOrder I] [LinearOrder O] (D : CollapseData I O) (BH : O),
    TowerHypotheses D → D.psi D.endpoint = BH →
    ∀ θ, IsLUB (Set.range (fun n => D.psi (D.a n))) θ → θ = D.psi D.endpoint ∧ θ = BH

end LogicLineages.PersistentMarking.ConditionalTowerCofinality
