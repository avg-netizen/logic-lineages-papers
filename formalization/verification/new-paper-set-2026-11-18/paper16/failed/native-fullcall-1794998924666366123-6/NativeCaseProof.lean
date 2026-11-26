import LogicLineages.PersistentMarking.NativeTypingProof
import LogicLineages.PersistentMarking.SubstitutionProof
namespace LogicLineages.PersistentMarking.NativeCaseProof
open Spine NativeReduction NativeTypingProof

theorem casePaper (S : Signature) (τ : Ty) (u A B : Expr)
    (hu : PaperTerm S u .ground) (hA : PaperTerm S A τ) (hB : PaperTerm S B τ) :
    PaperTerm S (caseTerm τ u A B) τ :=
  appPaper S _ _ _ _ (appPaper S _ _ _ _ (appPaper S _ _ _ _ (caseConstantPaper S τ) hu) hA) hB

theorem caseOrdinary (τ : Ty) (u A B : Expr) (hu : Ordinary u) (hA : Ordinary A) (hB : Ordinary B) :
    Ordinary (caseTerm τ u A B) := ⟨⟨⟨True.intro,hu,True.intro⟩,hA,True.intro⟩,hB,True.intro⟩

theorem caseAWeak (S : Signature) (τ : Ty) (u A B : Expr)
    (hu : PaperTerm S u .ground) (hA : PaperTerm S A τ) (hB : PaperTerm S B τ) (hoA : Ordinary A) :
    Weak S (.marked (.app τ τ) τ
      (.cons (app τ (.arrow τ τ) (app .ground (.arrow τ (.arrow τ τ)) (.head (.case τ) .nil) u) A) (.cons B .nil)) .nil) A := by
  let U := app .ground (.arrow τ (.arrow τ τ)) (.head (.case τ) .nil) u
  let V := app τ (.arrow τ τ) U A
  let owner := Expr.marked (.app τ τ) τ (.cons V (.cons B .nil)) .nil
  let inner := Expr.marked (.app τ (.arrow τ τ)) τ (.cons U (.cons A .nil)) (.cons owner .nil)
  have hU : PaperTerm S U (.arrow τ (.arrow τ τ)) := appPaper S _ _ _ _ (caseConstantPaper S τ) hu
  have hV : PaperTerm S V (.arrow τ τ) := appPaper S _ _ _ _ hU hA
  have howner : PaperTerm S owner τ := markedAppPaper S τ τ τ V B .nil hV hB .nil True.intro
  have hcall : apply V (ownerCopies (.app τ τ) (.cons V (.cons B .nil)) .nil [τ]) = some inner := by
    simp [V,inner,owner,app,ownerCopies,apply,applyAux,consumeTypes,Head.result,Expr.type,SubstitutionProof.emptyArgsSubstitution]
  exact .select (domains := [τ]) howner hA (Or.inl .here) hV.1 hcall
    (secondSelect S τ (.arrow τ τ) U A (.cons owner .nil) hU hA hoA (.cons howner.1 .nil) ⟨howner.2,True.intro⟩)

theorem caseZero : NativeOrientationTargets.CaseZero := by
  intro S τ A B hA hoA hB hoB
  have hs := casePaper S τ zero A B (zeroPaper S) hA hB
  have hos := caseOrdinary τ zero A B True.intro hoA hoB
  refine ⟨⟨τ,hs,hA,hos,hoA⟩,Strict.intro hs hA rfl (caseAWeak S τ zero A B (zeroPaper S) hA hB hoA),?_⟩
  intro ρ h
  exact leftIncluded τ τ _ B ρ (rightIncluded τ (.arrow τ τ) _ A ρ h)

theorem caseSucc : NativeOrientationTargets.CaseSucc := by
  intro S τ n A B hn hon hA hoA hB hoB
  have hsn := succPaper S n hn
  have hU := appPaper S _ _ _ _ (caseConstantPaper S τ) hsn
  have hV := appPaper S _ _ _ _ hU hA
  have hs := casePaper S τ (succ n) A B hsn hA hB
  have hos := caseOrdinary τ (succ n) A B ⟨True.intro,hon,True.intro⟩ hoA hoB
  exact ⟨⟨τ,hs,hB,hos,hoB⟩,Strict.intro hs hB rfl (secondSelect S τ τ _ B .nil hV hB hoB .nil True.intro),
    rightIncluded τ τ _ B⟩

theorem recZero : NativeOrientationTargets.RecZero := by
  intro S τ A B hA hoA hB hoB
  have hV := rec2Paper S τ zero A (zeroPaper S) hA
  have hs := recPaper S τ zero A B (zeroPaper S) hA hB
  have hos : Ordinary (recTerm τ zero A B) := ⟨⟨⟨True.intro,True.intro,True.intro⟩,hoA,True.intro⟩,hoB,True.intro⟩
  exact ⟨⟨τ,hs,hB,hos,hoB⟩,Strict.intro hs hB rfl (secondSelect S τ τ _ B .nil hV hB hoB .nil True.intro),
    rightIncluded τ τ _ B⟩
end LogicLineages.PersistentMarking.NativeCaseProof
