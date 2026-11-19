import LogicLineages.PersistentMarking.NumberedWindowTupleAuxGoals
import LogicLineages.PersistentMarking.NumberedWindowTupleHeadProof
import LogicLineages.PersistentMarking.SpineCallTypingProof

namespace LogicLineages.PersistentMarking.NumberedWindowTupleAuxHeadCases
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowTupleTargets
open NumberedWindowTupleAuxGoals NumberedWindowSourceGuardTargets

theorem ordinaryCase (S : Signature) (K : List Ty) (C : BoundContext) (n B : Nat)
    (a : Expr) (rest : Spine.Args) (f : Head) (bs : Spine.Args) :
    AtArgs S K C n B (.cons a rest) (.head f bs) := by
  intro values types σ τ r Q As Vs hk hBudget hW hV hCall hv hu hr hRep hAs hVs
  have hn : n ≤ B := by omega
  have hNum := substituteWindow hW hV hRep hVs
  cases hW.1 with
  | head hBs =>
    have hc := SpineCallTypingProof.consumeExact C f.result _ τ hCall
    simp only [Spine.applyAux,hc,Option.map_some,Option.some.injEq] at hr
    subst r
    obtain ⟨ds,hArrow,_,hArgsW⟩ := NumberedWindowApplicationChecks.exact_RealizedCallArgs S K C
      f.result τ _ As B hCall hv hu hAs
    cases hRep with
    | ordinary hBsRep =>
      exact NumberedWindowTupleHeadProof.ordinary hk hArrow hNum hArgsW
        (NumberedWindowRealizationSubstitutionProof.args hVs hBsRep 0) hAs hn

theorem markedCase (S : Signature) (K : List Ty) (C : BoundContext) (n B : Nat)
    (a : Expr) (rest : Spine.Args) (f : Head) (δ : Ty) (bs es : Spine.Args) :
    AtArgs S K C n B (.cons a rest) (.marked f δ bs es) := by
  intro values types σ τ r Q As Vs hk hBudget hW hV hCall hv hu hr hRep hAs hVs
  have hn : n ≤ B := by omega
  have hNum := substituteWindow hW hV hRep hVs
  cases hW.1 with
  | marked hb he =>
    have hc := SpineCallTypingProof.consumeExact C δ _ τ hCall
    simp only [Spine.applyAux,hc,Option.map_some,Option.some.injEq] at hr
    subst r
    obtain ⟨ds,hArrow,hLength,hArgsW⟩ := NumberedWindowApplicationChecks.exact_RealizedCallArgs S K C
      δ τ _ As B hCall hv hu hAs
    cases hRep with
    | marked hLabel hBsRep hEsRep =>
      exact NumberedWindowTupleHeadProof.marked hk hArrow hNum hArgsW
        (NumberedWindowRealizationSubstitutionProof.args hVs hBsRep 0)
        (NumberedWindowRealizationSubstitutionProof.args hVs hEsRep 0) hAs hn (by omega)

end LogicLineages.PersistentMarking.NumberedWindowTupleAuxHeadCases
