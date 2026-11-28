module

public import LogicLineages.NativeModule.PersistentMarking.Paper16RemainingOrdinalTargets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformTargets

@[expose] public section

/-! # The least norm bound of the formal ID₁ calculus exists

Frozen before proof (local Fable-trio round, 27 November 2026, root lane).

`Paper16RemainingOrdinalTargets.LeastNormBound β` says: every atom `I(n)` derivable in the
formal calculus for a positive body has an inductive stage below `β`, and `β` is the least such
ordinal. The statements below say that this ordinal exists (it is at most `ω₁`), is unique, and
can stand where the printed proofs apply the cited norm theorem. They do **not** identify it
with the Bachmann–Howard ordinal or with the collapse endpoint `ψ_B(ε_{Ω+1})`: the inequality
`β ≤ ψ_B(ε_{Ω+1})` is exactly the cited theorem and stays an input. -/

namespace LogicLineages.PersistentMarking.Paper16LeastNormBoundTargets
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus
open NumberedWindowExternalIDOperators NumberedWindowExternalIDStages
open ExternalOrdinalInterfaceID1Targets Paper16RemainingOrdinalTargets
open ConditionalUpperUniformTargets (UniformAccessibility)
open ConditionalHeightTargets (descendingHeight nativeHeight)
open Spine NativeIteratorStrictTargets NativeIndexedCarrierTargets NativeRankTargets
open scoped Ordinal

/-- The stages of a monotone operator on the naturals, taken along the countable ordinals,
exhaust its least pre-fixed predicate. -/
def StagesExhaustLeast : Prop :=
  ∀ F : Operator, IsMonotone F → ∀ n, Least F n →
    ∃ a : Ordinal.{0}, a < ω₁ ∧ stage (· < ·) Ordinal.lt_wf F a n

/-- The operator of a positive body is monotone. -/
def BodyOperatorMonotone : Prop :=
  ∀ B : Positive (Fin 1), IsMonotone (bodyOperator B)

/-- Soundness in stage form: a derivable atom lies in a countable stage of its body. -/
def DerivableAtomsHaveStages : Prop :=
  ∀ (B : Positive (Fin 1)) (n : Nat),
    Nonempty (Derivation B [] (Positive.predicate (α := Empty) (numeral n)).formula) →
    ∃ a : Ordinal.{0}, a < ω₁ ∧ stage (· < ·) Ordinal.lt_wf (bodyOperator B) a n

/-- `ω₁` is a norm bound. -/
def NormTheoremAtOmegaOne : Prop := NormTheorem ω₁

/-- The least norm bound exists and is at most `ω₁`. -/
def LeastNormBoundExists : Prop := ∃ β : Ordinal.{0}, LeastNormBound β ∧ β ≤ ω₁

def LeastNormBoundUnique : Prop :=
  ∀ β γ : Ordinal.{0}, LeastNormBound β → LeastNormBound γ → β = γ

/-- An ordinal satisfies the norm theorem exactly when it is at least the least norm bound. -/
def NormTheoremIffAbove : Prop :=
  ∀ β : Ordinal.{0}, LeastNormBound β → ∀ γ : Ordinal.{0}, NormTheorem γ ↔ β ≤ γ

/-- `thm:upper` at the least norm bound needs accessibility only. -/
def UpperAtLeastNormBound : Prop :=
  ∀ β : Ordinal.{0}, LeastNormBound β → UniformAccessibility →
    ConditionalUpperTargets.UpperStatement β

/-- With accessibility and the pointwise calibration, both heights lie between the collapse
endpoint and the least norm bound. -/
def HeightsBetween : Prop :=
  ∀ β : Ordinal.{0}, LeastNormBound β → UniformAccessibility → AllTowerCalibration →
    ∀ (A : OrdinalSemantics) (S : Signature)
      (wfFull : WellFounded (fun t s : Expr => ConfinedPair.Strict S s t))
      (wfNative : WellFounded (@NativeBelow S indexType)),
      A.endpointValue ≤ nativeHeight S wfNative ∧
      nativeHeight S wfNative ≤ descendingHeight S wfFull ∧
      descendingHeight S wfFull ≤ β

/-- Hence the collapse endpoint is at most the least norm bound: the lower half of the cited
identification follows from the paper's own two inputs. -/
def EndpointBelowLeastNormBound : Prop :=
  ∀ β : Ordinal.{0}, LeastNormBound β → UniformAccessibility → AllTowerCalibration →
    ∀ A : OrdinalSemantics, A.endpointValue ≤ β

end LogicLineages.PersistentMarking.Paper16LeastNormBoundTargets
