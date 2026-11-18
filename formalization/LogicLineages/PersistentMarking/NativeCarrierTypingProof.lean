import LogicLineages.PersistentMarking.NativeCarrierTargets
import LogicLineages.PersistentMarking.NativeTypingProof
import LogicLineages.PersistentMarking.SubstitutionProof

namespace LogicLineages.PersistentMarking.NativeCarrierTypingProof
open Spine NativeReduction NativeTypingProof NativeCarrierTargets

theorem closedTyped (C : BoundContext) (q : Expr) (σ : Ty) (h : Typed EmptyContext q σ) : Typed C q σ := by
  have hc : ShiftCompatible 0 0 EmptyContext C := by
    intro i τ hi
    cases hi
  simpa only [SubstitutionProof.shiftZero] using SpineShiftProof.shiftPreserves EmptyContext C q σ 0 0 h hc

theorem liftedPaper (S : Signature) (B : Ty) (K : Expr) (hK : PaperTerm S K (.arrow B B)) :
    PaperTerm S (lifted K) (stepType B) :=
  ⟨.lam (closedTyped (EmptyContext.push .ground) K (.arrow B B) hK.1),hK.2⟩

structure Family (S : Signature) (B : Ty) (K U : Expr) : Prop where
  w : PaperTerm S (W B K U) B
  q : ∀ ρ, PaperTerm S (Q B K U ρ) ρ
  c2 : ∀ ρ, PaperTerm S (C₂ B K U ρ) ρ
  c1 : ∀ ρ, PaperTerm S (C₁ B K U ρ) ρ
  c0 : ∀ ρ, PaperTerm S (C₀ B K U ρ) ρ

theorem family (S : Signature) (B : Ty) (K U : Expr)
    (hK : PaperTerm S K (.arrow B B)) (hU : PaperTerm S U B) : Family S B K U := by
  let F := lifted K
  have hF := liftedPaper S B K hK
  have hz := zeroPaper S
  have h0 := recConstantPaper S B
  have h1 := rec1Paper S B zero hz
  have h2 := rec2Paper S B zero F hz hF
  have hq : ∀ ρ, PaperTerm S (Q B K U ρ) ρ :=
    fun ρ => markedAppPaper S B B ρ _ U .nil h2 hU .nil True.intro
  have hc2 : ∀ ρ, PaperTerm S (C₂ B K U ρ) ρ := fun ρ =>
    markedAppPaper S (stepType B) (.arrow B B) ρ _ F (c2Extras B K U) h1 hF
      (.cons (hq B).1 .nil) ⟨(hq B).2,True.intro⟩
  have hc1 : ∀ ρ, PaperTerm S (C₁ B K U ρ) ρ := fun ρ =>
    markedAppPaper S .ground (.arrow (stepType B) (.arrow B B)) ρ _ zero (c1Extras B K U) h0 hz
      (.cons (hc2 (stepType B)).1 (.cons (hc2 B).1 .nil)) ⟨(hc2 (stepType B)).2,(hc2 B).2,True.intro⟩
  have hc0 : ∀ ρ, PaperTerm S (C₀ B K U ρ) ρ := fun ρ =>
    ⟨.marked .nil (.cons (hc1 .ground).1 (.cons (hc1 (stepType B)).1 (.cons (hc1 B).1 .nil))),
      ⟨1,rfl⟩,True.intro,(hc1 .ground).2,(hc1 (stepType B)).2,(hc1 B).2,True.intro⟩
  exact ⟨recPaper S B zero F U hz hF hU,hq,hc2,hc1,hc0⟩

theorem ordinary (B : Ty) (K U : Expr) (hK : Ordinary K) (hU : Ordinary U) :
    Ordinary (W B K U) :=
  ⟨⟨⟨True.intro,True.intro,True.intro⟩,hK,True.intro⟩,hU,True.intro⟩

theorem markW (B : Ty) (K U : Expr) : mark (W B K U) = some (Q B K U B) := rfl

end LogicLineages.PersistentMarking.NativeCarrierTypingProof
