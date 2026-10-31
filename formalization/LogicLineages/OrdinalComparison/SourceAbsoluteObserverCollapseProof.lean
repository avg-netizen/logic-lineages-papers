module
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverAnchorProof
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverUnusedProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AbsoluteObserver.Proof
open AdmissibleAssignment ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem source_head_extraction {Γ τ} (hΓ : ∀ σ ∈ Γ, σ = Ty.ground)
    (t : OriginalTerm Γ τ) (v : OrdinalVector Γ τ.level)
    (hv : assignment OrdinalSyntax.defaultPolicy t = some v)
    (a b : OrdinalExpression Γ) (he : v 0 = .collapse a b) :
    ∃ c, extractPositive a = some c := by
  obtain ⟨w, hw, hg⟩ := actualAdmissibleAssignmentGenerated Γ τ OrdinalSyntax.defaultPolicy t
  have h := Option.some.inj (hw.symm.trans hv)
  subst w
  obtain ⟨s, hs⟩ := generatedGroundScalarTranslationTotal Γ hΓ (v 0) (hg 0)
  rw [he] at hs
  simp only [compileScalar] at hs
  cases hc : extractPositive a with
  | none => simp [hc] at hs
  | some c => exact ⟨c,rfl⟩

theorem collapse_cancel {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (a b d e : OrdinalExpression Γ) (c : ClosedPositive)
    (hc : extractPositive a = some c) (hab : denote ν a = denote ν b)
    (n m : Nat) (hd : denote ν d = (n : Ordinal)) (he : denote ν e = (m : Ordinal)) :
    denote ν (.collapse a d) = denote ν (.collapse b e) ↔ n = m := by
  have hv := closedPositiveEvaluationSound Γ a c hc ν
  have ha := (scalarFixedHeadAdmissible c).2
  simp only [denote, hd, he, ← hab, ← hv]
  rw [actualNaturalSumFiniteRight _ n, actualNaturalSumFiniteRight _ m]
  change (actualCollapse (fixedHead c + (n : Ordinal)) : Ordinal) =
      (actualCollapse (fixedHead c + (m : Ordinal)) : Ordinal) ↔ n = m
  constructor
  · intro h
    exact (collapse_tail_strict _ ha).injective (Nat.cast_injective h)
  · rintro rfl
    rfl

theorem numeral_value {Γ} (ν : OrdinalComponent Γ → Ordinal) (n : Nat) :
    denote ν (numeral OrdinalSyntax.defaultPolicy n) = (n : Ordinal) := by
  cases n with
  | zero => simp [numeral, repeated, denote]
  | succ n =>
    simp only [numeral, repeated]
    rw [AdmissibleSum.expand_value]
    simp only [List.ofFn_const, List.map_replicate, denote]
    simpa only [Nat.mul_one, Nat.cast_one] using values_repeat (n+1) 1

theorem box_tail_value {Γ} (ν : OrdinalComponent Γ → Ordinal) (k n m : Nat)
    (a b : OrdinalExpression Γ) (ha : denote ν a = (n : Ordinal)) (hb : denote ν b = (m : Ordinal)) :
    denote ν (boxTail OrdinalSyntax.defaultPolicy k a b) = ((n+m+k : Nat) : Ordinal) := by
  by_cases hk : k=0
  · subst k
    simp only [boxTail, ↓reduceIte, denote, ha, hb, naturalSum_finite, Nat.add_zero]
  · have ht : boxTail OrdinalSyntax.defaultPolicy k a b = .add a (.add b (numeral OrdinalSyntax.defaultPolicy k)) := by
      simp [boxTail, hk, AdmissiblePartial.three, OrdinalSyntax.defaultPolicy,
        OrdinalSyntax.defaultShape, AdmissibleSum.expand]
    rw [ht]
    simp only [denote, ha, hb, numeral_value, naturalSum_finite, Nat.add_assoc]

theorem application_scalar {Γ σ τ} (f : OrdinalVector Γ (Ty.arrow σ τ).level)
    (g : OrdinalVector Γ σ.level) :
    application OrdinalSyntax.defaultPolicy f g 0 =
      .collapse (ordinalBoxPositive σ.level (ordinalVectorAt f) (ordinalVectorAt g) 1)
        (boxTail OrdinalSyntax.defaultPolicy σ.level (f 0) (g 0)) := rfl
end LogicLineages.OrdinalComparison.Source.AbsoluteObserver.Proof
