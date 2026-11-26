import LogicLineages.PersistentMarking.NumberedWindowTupleHeadProof
import LogicLineages.PersistentMarking.NumberedWindowTupleBetaProof
import LogicLineages.PersistentMarking.SpineCallTypingProof

namespace LogicLineages.PersistentMarking.NumberedWindowTupleAuxProof
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowTupleTargets
open NumberedWindowApplicationTargets NumberedWindowSourceGuardTargets NumberedWindowTupleBridgeProof
open NumberedWindowRealizationShapeProof
open DecisionInventory (auxiliarySupport auxiliaryArgs)

theorem aux (S : Signature) (K : List Ty) (C : BoundContext) (n B : Nat)
    (q : Expr) (args values : Spine.Args) (types : List Ty) (σ τ : Ty) (r : Expr)
    (Q : NTerm) (As Vs : NArgs) (hk : DecisionSourceUniverse.Closed K)
    (hBudget : n + args.length + 1 ≤ B)
    (hW : SourceGuard S K (BoundContext.prefix types C) σ q)
    (hV : SourceValues S K C types values)
    (hCall : CallTyped C σ args τ) (hv : ValidArgs S args)
    (hu : SymbolicArgsAdmissible K args)
    (hr : Spine.applyAux q args values = some r)
    (hRep : Realizes B q Q) (hAs : RealizesArgs B args As) (hVs : RealizesArgs B values Vs) :
    Conclusion S K C n τ (NumberedWindowSyntax.substitute Vs 0 Q) As r := by
  have hn : n ≤ B := by omega
  have hSubW := NumberedWindowSourceGuardChecks.exact_ActualBlockGuard S K C types values q σ hW hV
  have hSubR := NumberedWindowRealizationSubstitutionProof.term hVs hRep 0
  have hNum := NumberedWindowRealizationChecks.exact_RealizationInWindow S K C σ B _ _
    hSubW.1 hSubW.2.1 hSubW.2.2 hSubR
  cases args with
  | nil =>
    cases hCall
    cases hAs
    simp only [Spine.applyAux,Option.some.injEq] at hr
    subst r
    exact ⟨_,_,rfl,.refl hNum,weakensTerm hn hSubR⟩
  | cons a rest =>
    cases q with
    | free δ x => simp [Spine.applyAux] at hr
    | bound δ i => simp [Spine.applyAux] at hr
    | lam α body =>
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
              have hBodyW := NumberedWindowSourceGuardChecks.exact_ActualBlockGuard S K C _ _ _ _ hBodyGuard hV'
              have hBodyNum := NumberedWindowRealizationChecks.exact_RealizationInWindow S K C _ B _ _
                hBodyW.1 hBodyW.2.1 hBodyW.2.2 (NumberedWindowRealizationSubstitutionProof.term hVs' hBodyR 0)
              have hANum := NumberedWindowRealizationChecks.exact_RealizationInWindow S K C _ B _ _
                hArg.1 hArg.2.1 hArg.2.2 hAR
              obtain ⟨ds,hArrow,_,hTailW⟩ := NumberedWindowApplicationChecks.exact_RealizedCallArgs S K C _ _
                rest _ B hTailT hv.2 hTailSupp hTailR
              have tail := aux S K C n B body rest (.cons a values) (α::types) _ τ r _ _ _
                hk hBudget' hBodyGuard hV' hTailT hv.2 hTailSupp hApply hBodyR hTailR hVs'
              exact NumberedWindowTupleBetaProof.prependBeta hk hArrow hNum hANum hBodyNum hTailW tail
    | head f bs =>
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
    | marked f δ bs es =>
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
termination_by sizeOf args

end LogicLineages.PersistentMarking.NumberedWindowTupleAuxProof
