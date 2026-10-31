module
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionScalarProof
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionEraserProof
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionNumericProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceCollisionCompletion.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open OriginalDomain
open SourceAdditionCompletion.Proof

theorem eraser_denotation {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (a b : OrdinalExpression Γ) (x y : Nat)
    (ha : denote ν a = (x : Ordinal)) (hb : denote ν b = (y : Ordinal)) :
    denote ν (eraserVector a b 0) = (g (3*x+y+2) : Ordinal) := by
  have h1 : denote ν (.one : OrdinalExpression Γ) = ((1 : Nat) : Ordinal) := by simp [denote]
  have ha1 := add_value ν _ _ _ _ ha h1
  have haa := add_value ν _ _ _ _ ha1 ha1
  have haaa := add_value ν _ _ _ _ haa ha
  have ht := add_value ν _ _ _ _ haaa hb
  have hc := collapse_one_value ν _ _ ht
  rw [g_calibration]
  have hn : x+1+(x+1)+x+y+2 = 3*x+y+2+2 := by omega
  simpa only [eraserVector, inflated, hn] using hc

theorem actualGroundEraser : Targets.ActualGroundEraser := by
  intro Γ p q ρ
  obtain ⟨vp, hp, sp⟩ := actualScalarTotal Γ p
  obtain ⟨vq, hq, sq⟩ := actualScalarTotal Γ q
  have he := eraser_assignment p q vp vq hp hq
  exact raw_of_assignment (valuation ρ) (eraser p q) _ _ he
    (eraser_denotation (valuation ρ) (vp 0) (vq 0) _ _ (sp ρ).1 (sq ρ).1)

theorem admissible_collision (Γ : List Ty) (p q : OriginalTerm Γ .ground)
    (ρ : AdmissibleSubstitution Γ) : CollisionAt (valuation ρ) p q := by
  have hl : rawScalar (valuation ρ) (detectorLeft p q) =
      leftValue (rawScalar (valuation ρ) p) (rawScalar (valuation ρ) q) := by
    unfold detectorLeft leftValue
    rw [actualGroundEraser Γ (eraser p p) (eraser q q) ρ,
      actualGroundEraser Γ p p ρ, actualGroundEraser Γ q q ρ]
  have hr : rawScalar (valuation ρ) (detectorRight p q) =
      rightValue (rawScalar (valuation ρ) p) (rawScalar (valuation ρ) q) := by
    unfold detectorRight rightValue
    rw [actualGroundEraser Γ (eraser p q) (eraser q p) ρ,
      actualGroundEraser Γ p q ρ, actualGroundEraser Γ q p ρ]
  unfold CollisionAt
  rw [hl, hr]
  exact numeric_collision _ _
end LogicLineages.OrdinalComparison.Source.SourceCollisionCompletion.Proof
