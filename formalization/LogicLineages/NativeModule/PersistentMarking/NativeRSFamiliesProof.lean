module

public import LogicLineages.NativeModule.PersistentMarking.NativeTypingProof
public import LogicLineages.NativeModule.PersistentMarking.NativeFullCallProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeRSFamiliesProof
open Spine NativeReduction NativeTypingProof

structure FamilyTyping (S : Signature) (τ : Ty) (n A B : Expr) : Prop where
  p : ∀ ρ, PaperTerm S (P τ n A B ρ) ρ
  c2 : ∀ ρ, PaperTerm S (C2 τ n A B ρ) ρ
  c1 : ∀ ρ, PaperTerm S (C1 τ n A B ρ) ρ
  c0 : ∀ ρ, PaperTerm S (C0 τ n A B ρ) ρ

theorem familyTyping (S : Signature) (τ : Ty) (n A B : Expr)
    (hn : PaperTerm S n .ground) (hA : PaperTerm S A (stepType τ)) (hB : PaperTerm S B τ) :
    FamilyTyping S τ n A B := by
  have hsn := succPaper S n hn
  have hU1 := rec1Paper S τ (succ n) hsn
  have hU2 := rec2Paper S τ (succ n) A hsn hA
  have hp : ∀ ρ, PaperTerm S (P τ n A B ρ) ρ := fun ρ => markedAppPaper S τ τ ρ _ B .nil hU2 hB .nil True.intro
  have hc2 : ∀ ρ, PaperTerm S (C2 τ n A B ρ) ρ := fun ρ =>
    markedAppPaper S (stepType τ) (.arrow τ τ) ρ _ A (.cons (P τ n A B τ) .nil) hU1 hA
      (.cons (hp τ).1 .nil) ⟨(hp τ).2,True.intro⟩
  have hc1 : ∀ ρ, PaperTerm S (C1 τ n A B ρ) ρ := fun ρ =>
    markedAppPaper S .ground (.arrow (stepType τ) (.arrow τ τ)) ρ _ (succ n)
      (.cons (C2 τ n A B (stepType τ)) (.cons (C2 τ n A B τ) .nil)) (recConstantPaper S τ) hsn
      (.cons (hc2 (stepType τ)).1 (.cons (hc2 τ).1 .nil)) ⟨(hc2 (stepType τ)).2,(hc2 τ).2,True.intro⟩
  have hc0 : ∀ ρ, PaperTerm S (C0 τ n A B ρ) ρ := fun ρ =>
    ⟨.marked .nil (.cons (hc1 .ground).1 (.cons (hc1 (stepType τ)).1 (.cons (hc1 τ).1 .nil))),
      ⟨1,rfl⟩,True.intro,⟨(hc1 .ground).2,(hc1 (stepType τ)).2,(hc1 τ).2,True.intro⟩⟩
  exact ⟨hp,hc2,hc1,hc0⟩

theorem recOrdinary (τ : Ty) (u A B : Expr) (hu : Ordinary u) (hA : Ordinary A) (hB : Ordinary B) :
    Ordinary (recTerm τ u A B) := ⟨⟨⟨True.intro,hu,True.intro⟩,hA,True.intro⟩,hB,True.intro⟩

theorem prefixSelections (S : Signature) (τ : Ty) (n A B target : Expr)
    (hn : PaperTerm S n .ground) (hA : PaperTerm S A (stepType τ)) (hB : PaperTerm S B τ)
    (ht : PaperTerm S target τ) (hw : Weak S (C0 τ n A B τ) target) : Weak S (P τ n A B τ) target := by
  have hf := familyTyping S τ n A B hn hA hB
  have hsn := succPaper S n hn
  have h1 : Weak S (C1 τ n A B τ) target :=
    .select (domains := [.ground,stepType τ,τ]) (hf.c1 τ) ht (Or.inl .here)
      (recConstantPaper S τ).1 (NativeFullCallProof.thirdFullCall τ n A B) hw
  have h2 : Weak S (C2 τ n A B τ) target :=
    .select (domains := [stepType τ,τ]) (hf.c2 τ) ht (Or.inl .here)
      (rec1Paper S τ (succ n) hsn).1 (NativeFullCallProof.secondFullCall τ n A B) h1
  exact .select (domains := [τ]) (hf.p τ) ht (Or.inl .here)
    (rec2Paper S τ (succ n) A hsn hA).1 (NativeFullCallProof.firstFullCall τ n A B) h2
end LogicLineages.PersistentMarking.NativeRSFamiliesProof
