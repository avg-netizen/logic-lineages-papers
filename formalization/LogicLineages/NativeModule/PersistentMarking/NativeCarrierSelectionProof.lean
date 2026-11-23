module

public import LogicLineages.NativeModule.PersistentMarking.NativeCarrierTypingProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeCarrierSelectionProof
open Spine NativeReduction NativeTypingProof NativeCarrierTargets NativeCarrierTypingProof

theorem firstCall (B : Ty) (K U : Expr) :
    apply (rec2 B zero (lifted K)) (ownerCopies (.app B B) (qBase B K U) .nil [B]) =
      some (C₂ B K U B) := by
  simp [rec2,app,apply,applyAux,consumeTypes,Head.result,Q,C₂,c2Base,c2Extras,Expr.type,
    ownerCopies,SubstitutionProof.emptyArgsSubstitution]

theorem secondCall (B : Ty) (K U : Expr) :
    apply (rec1 B zero)
      (ownerCopies (.app (stepType B) (.arrow B B)) (c2Base B K) (c2Extras B K U) [stepType B,B]) =
      some (C₁ B K U B) := by
  simp [rec1,app,apply,applyAux,consumeTypes,Head.result,C₂,C₁,c1Base,c1Extras,Expr.type,
    ownerCopies,SubstitutionProof.emptyArgsSubstitution]

theorem thirdCall (B : Ty) (K U : Expr) :
    apply (.head (.recursor B) .nil)
      (ownerCopies (.app .ground (.arrow (stepType B) (.arrow B B))) (c1Base B) (c1Extras B K U)
        [.ground,stepType B,B]) = some (C₀ B K U B) := by
  simp [apply,applyAux,consumeTypes,C₁,C₀,c0Extras,Head.result,stepType,Expr.type,ownerCopies,
    SubstitutionProof.emptyArgsSubstitution]

theorem toU (S : Signature) (B : Ty) (K U : Expr)
    (hK : PaperTerm S K (.arrow B B)) (hU : PaperTerm S U B) (hoU : Ordinary U) :
    Weak S (Q B K U B) U :=
  secondSelect S B B (rec2 B zero (lifted K)) U .nil
    (rec2Paper S B zero (lifted K) (zeroPaper S) (liftedPaper S B K hK)) hU hoU .nil True.intro

theorem toTarget (S : Signature) (B : Ty) (K U T : Expr)
    (hFam : Family S B K U) (ht : PaperTerm S T B) (hw : Weak S (Q B K U B) T) :
    Weak S (C₀ B K U B) T := by
  have hc2 : Weak S (C₂ B K U B) T :=
    .select (domains := []) (hFam.c2 B) ht (Or.inr .here) (hFam.q B).1 rfl hw
  have hc1 : Weak S (C₁ B K U B) T :=
    .select (domains := []) (hFam.c1 B) ht (Or.inr (.there .here)) (hFam.c2 B).1 rfl hc2
  exact .select (domains := []) (hFam.c0 B) ht (Or.inr (.there (.there .here))) (hFam.c1 B).1 rfl hc1

theorem prefixSelections (S : Signature) (B : Ty) (K U T : Expr)
    (hK : PaperTerm S K (.arrow B B)) (hFam : Family S B K U) (ht : PaperTerm S T B)
    (hw : Weak S (C₀ B K U B) T) : Weak S (Q B K U B) T := by
  have hc1 : Weak S (C₁ B K U B) T :=
    .select (domains := [.ground,stepType B,B]) (hFam.c1 B) ht (Or.inl .here)
      (recConstantPaper S B).1 (thirdCall B K U) hw
  have hc2 : Weak S (C₂ B K U B) T :=
    .select (domains := [stepType B,B]) (hFam.c2 B) ht (Or.inl .here)
      (rec1Paper S B zero (zeroPaper S)).1 (secondCall B K U) hc1
  exact .select (domains := [B]) (hFam.q B) ht (Or.inl .here)
    (rec2Paper S B zero (lifted K) (zeroPaper S) (liftedPaper S B K hK)).1 (firstCall B K U) hc2

end LogicLineages.PersistentMarking.NativeCarrierSelectionProof
