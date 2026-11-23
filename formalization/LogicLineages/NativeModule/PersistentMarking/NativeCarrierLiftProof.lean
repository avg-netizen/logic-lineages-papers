module

public import LogicLineages.NativeModule.PersistentMarking.NativeCarrierSelectionProof
public import LogicLineages.NativeModule.PersistentMarking.RefinementAppendProof
public import LogicLineages.NativeModule.PersistentMarking.ClosedSyntaxProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeCarrierLiftProof
open Spine NativeReduction NativeTypingProof NativeCarrierTargets NativeCarrierTypingProof

def extendedC1Extras (B : Ty) (K U : Expr) : Args :=
  (c1Extras B K U).append (.cons (C₀ B K U .ground) .nil)
def extendedC1 (B : Ty) (K U : Expr) (ρ : Ty) : Expr :=
  .marked (.app .ground (.arrow (stepType B) (.arrow B B))) ρ (c1Base B) (extendedC1Extras B K U)
def extendedC2Extras (B : Ty) (K U : Expr) : Args :=
  (c2Extras B K U).append (.cons (extendedC1 B K U .ground) .nil)
def extendedC2 (B : Ty) (K U : Expr) (ρ : Ty) : Expr :=
  .marked (.app (stepType B) (.arrow B B)) ρ (c2Base B K) (extendedC2Extras B K U)

theorem callC1 (B : Ty) (K U : Expr) :
    apply (C₁ B K U (stepType B)) (ownerCopies (.recursor B) .nil (c0Extras B K U) [.ground]) =
      some (extendedC1 B K U (.arrow B B)) := by
  simp [C₁,C₀,extendedC1,extendedC1Extras,apply,applyAux,consumeTypes,stepType,ownerCopies,
    Expr.type,SubstitutionProof.emptyArgsSubstitution]

theorem callC2 (B : Ty) (K U : Expr) :
    apply (C₂ B K U (stepType B))
      (ownerCopies (.app .ground (.arrow (stepType B) (.arrow B B))) (c1Base B) (extendedC1Extras B K U)
        [.ground]) = some (extendedC2 B K U (.arrow B B)) := by
  simp [C₂,extendedC1,extendedC2,extendedC2Extras,apply,applyAux,consumeTypes,stepType,ownerCopies,
    Expr.type,SubstitutionProof.emptyArgsSubstitution]

theorem callF (S : Signature) (B : Ty) (K U : Expr) (hK : PaperTerm S K (.arrow B B)) :
    apply (lifted K)
      (ownerCopies (.app (stepType B) (.arrow B B)) (c2Base B K) (extendedC2Extras B K U) [.ground]) =
      some K := by
  simp only [lifted,ownerCopies,apply,applyAux,Expr.type,if_true,
    ClosedSyntaxProof.closedSubstitute K (.arrow B B) hK.1]

theorem extendedC1Paper (S : Signature) (B : Ty) (K U : Expr)
    (h : Family S B K U) (ρ : Ty) : PaperTerm S (extendedC1 B K U ρ) ρ :=
  RefinementAppendProof.appendPaper S _ ρ ρ (c1Base B) (c1Extras B K U) _
    (h.c1 ρ) (.cons (h.c0 .ground).1 .nil) ⟨(h.c0 .ground).2,True.intro⟩

theorem extendedC2Paper (S : Signature) (B : Ty) (K U : Expr)
    (h : Family S B K U) (ρ : Ty) : PaperTerm S (extendedC2 B K U ρ) ρ :=
  RefinementAppendProof.appendPaper S _ ρ ρ (c2Base B K) (c2Extras B K U) _
    (h.c2 ρ) (.cons (extendedC1Paper S B K U h .ground).1 .nil)
    ⟨(extendedC1Paper S B K U h .ground).2,True.intro⟩

theorem toFunction (S : Signature) (B : Ty) (P K U : Expr)
    (hK : PaperTerm S K (.arrow B B)) (hP : PaperTerm S P (.arrow B B))
    (hFam : Family S B K U) (hKP : Weak S K P) :
    Weak S (C₀ B K U (.arrow B B)) P := by
  have hc2 : Weak S (extendedC2 B K U (.arrow B B)) P :=
    .select (domains := [.ground]) (extendedC2Paper S B K U hFam (.arrow B B)) hP
      (Or.inl (.there .here)) (liftedPaper S B K hK).1 (callF S B K U hK) hKP
  have hc1 : Weak S (extendedC1 B K U (.arrow B B)) P :=
    .select (domains := [.ground]) (extendedC1Paper S B K U hFam (.arrow B B)) hP
      (Or.inr .here) (hFam.c2 (stepType B)).1 (callC2 B K U) hc2
  exact .select (domains := [.ground]) (hFam.c0 (.arrow B B)) hP
    (Or.inr (.there .here)) (hFam.c1 (stepType B)).1 (callC1 B K U) hc1

end LogicLineages.PersistentMarking.NativeCarrierLiftProof
