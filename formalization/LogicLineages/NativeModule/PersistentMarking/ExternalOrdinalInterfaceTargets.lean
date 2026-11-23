module

public import LogicLineages.NativeModule.PersistentMarking.NativeTowerSequenceTargets
public import LogicLineages.NativeModule.PersistentMarking.NativeRankTargets
public import LogicLineages.PersistentMarking.ConditionalTowerCofinalityTargets

@[expose] public section

/-! # External inputs of Paper 16's ordinal sections, over abstract data

Nothing is defined concretely and nothing is asserted. The value order is `Ordinal.{0}` (every
value involved is a countable ordinal: ranks of terms, `Δ_n'`, `ψ_B(a_n)`, `BH`); the index order
`I` of the collapse (the paper's Ω-based arguments `a_n`, `Λ = ε_{Ω+1}`) stays abstract, as in
`ConditionalTowerCofinality.CollapseData` (#1463).

- E1 `Calibration`: the paper's composites `Δ_n'` (#1462) are the collapse values `ψ_B(a_n)`.
- E2: (P) and the facts the printed cofinality proof uses = `ConditionalTowerCofinality.TowerHypotheses`.
- E3 `BHIdentification`: `ψ_B(Λ) = BH`.
- `UpperBound`: the conclusion of `thm:upper` (second conjunct), as Opus B proves it from E4 and R1.
- E4 and R1 (ID₁ derivability, norm theorem) are in `ExternalOrdinalInterfaceID1Targets`, beside
  this module, because their vocabulary has a 700-module closure. -/

namespace LogicLineages.PersistentMarking.ExternalOrdinalInterfaceTargets
open Spine NativeIteratorStrictTargets NativeIndexedCarrierTargets OrdinalRealizationTargets
open OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets NativeTowerSequenceTargets NativeRankTargets
open ConditionalTowerCofinality

universe u

variable {I : Type u} [LinearOrder I]

/-- E1 (Simmons 2004 Thm 6.1 / Cor 6.2 with 2008 Thm 5.10, the identity after Lemma 6.6, and the
tameness remark): for some solution of the paper's arithmetic and ω equations, the paper's
composite `Δ_n'` equals the collapse value `ψ_B(a_n)` for every `n` ("satisfies Δ_n = ψ_B(a_n) by
the cited calibration"). -/
def Calibration (D : CollapseData I Ordinal.{0}) : Prop :=
  ∃ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul ∧ OmegaArithmeticEquations Z s mul w one pow fix ∧
    ∀ n, (sequenceValue fix pow w n).val = D.psi (D.a n)

/-- E3 (Pohlers §§9.4–9.5): "The Veblen-hull endpoint ψ_B(ε_{Ω+1}) is the BH of the
inductive-norm calibration." -/
def BHIdentification (D : CollapseData I Ordinal.{0}) (BH : Ordinal.{0}) : Prop :=
  D.psi D.endpoint = BH

/-- The conclusion of `thm:upper` (second conjunct): "rk_⊐(s) < BH for every ordinary term s",
the rank taken in the full confined strict relation of each signature. -/
def UpperBound (BH : Ordinal.{0}) : Prop :=
  ∀ S (wf : WellFounded (fun t s : Expr => ConfinedPair.Strict S s t)) (q : Expr) (τ : Ty),
    PaperTerm S q τ → Ordinary q → confinedRank (wf.apply q) < BH

end LogicLineages.PersistentMarking.ExternalOrdinalInterfaceTargets
