module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTupleAuxGoals
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTupleBetaProof
public import LogicLineages.NativeModule.PersistentMarking.SpineShiftProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowTupleAuxLambdaCase
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowTupleTargets
open NumberedWindowTupleAuxGoals NumberedWindowSourceGuardTargets NumberedWindowTupleBridgeProof
open DecisionInventory (auxiliarySupport auxiliaryArgs)

theorem lambdaCase (S : Signature) (K : List Ty) (C : BoundContext) (n B : Nat)
    (a : Expr) (rest : Spine.Args) (α : Ty) (body : Expr)
    (ih : ForArgs S K C n B rest) :
    AtArgs S K C n B (.cons a rest) (.lam α body) := by
  intro values types σ τ r Q As Vs hk hBudget hW hV hCall hv hu hr hRep hAs hVs
  have hNum := substituteWindow hW hV hRep hVs
  cases hW.1 with
  | lam hBody =>
    cases hCall with
    | cons hAT hTailT =>
      have hArg : SourceGuard S K C α a :=
        ⟨hAT,hv.1,fun ρ hρ => hu ρ (List.mem_append_left _ hρ)⟩
      have hTailSupp : SymbolicArgsAdmissible K rest :=
        fun ρ hρ => hu ρ (List.mem_append_right _ hρ)
      have hBodyGuard : SourceGuard S K (BoundContext.prefix (α::types) C) _ body :=
        ⟨hBody,hW.2.1,fun ρ hρ => hW.2.2 ρ (List.mem_append_right _ hρ)⟩
      have hV' := pushValues hArg hV
      have hType := SpineShiftProof.annotationExact _ _ _ hAT
      have hApply : Spine.applyAux body rest (.cons a values) = some r := by
        simpa only [Spine.applyAux,hType,if_true] using hr
      have hBudget' : n + rest.length + 1 ≤ B := by
        simp only [Spine.Args.length] at hBudget
        omega
      cases hAs with
      | cons hAR hTailR =>
        cases hRep with
        | lam hBodyR =>
          have hVs' := RealizesArgs.cons hAR hVs
          have hBodyNum := substituteWindow hBodyGuard hV' hBodyR hVs'
          have hANum := NumberedWindowRealizationChecks.exact_RealizationInWindow S K C _ B _ _
            hArg.1 hArg.2.1 hArg.2.2 hAR
          obtain ⟨ds,hArrow,_,hTailW⟩ := NumberedWindowApplicationChecks.exact_RealizedCallArgs S K C _ _
            rest _ B hTailT hv.2 hTailSupp hTailR
          have tail := ih body (.cons a values) (α::types) _ τ r _ _ _
            hk hBudget' hBodyGuard hV' hTailT hv.2 hTailSupp hApply hBodyR hTailR hVs'
          exact NumberedWindowTupleBetaProof.prependBeta hk hArrow hNum hANum hBodyNum hTailW tail

end LogicLineages.PersistentMarking.NumberedWindowTupleAuxLambdaCase
