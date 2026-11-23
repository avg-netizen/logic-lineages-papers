module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTupleAuxFoldProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowTupleSplitChecks
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowTupleTargets
open NumberedWindowSourceGuardTargets NumberedWindowTupleBridgeProof
open NumberedWindowRealizationShapeProof

theorem exact_WholeTupleSimulation : WholeTupleSimulation := by
  intro S K Γ q r args σ τ n Q As
  dsimp only
  intro hk hQ hValid hCall hArgsValid hAdmiss hArgsAdmiss hr hRep hAs
  let C := BoundContext.prefix Γ EmptyContext
  cases args with
  | nil =>
    cases hCall
    cases hAs
    simp only [Spine.apply,Option.some.injEq] at hr
    subst r
    have hW := NumberedWindowRealizationChecks.exact_RealizationInWindow S K C σ _ q Q
      hQ hValid hAdmiss hRep
    have hB : n ≤ budget n .nil := by simp [budget,Spine.Args.length]
    exact ⟨Q,Q,rfl,.refl hW,weakensTerm hB hRep⟩
  | cons a rest =>
    have hEmpty : SourceValues S K C [] .nil :=
      ⟨.nil,True.intro,fun _ h => False.elim (List.not_mem_nil h)⟩
    have h := NumberedWindowTupleAuxFoldProof.run S K C n (budget n (.cons a rest))
      (.cons a rest) q .nil [] σ τ r Q As .nil hk (Nat.le_refl _) ⟨hQ,hValid,hAdmiss⟩ hEmpty
      hCall hArgsValid hArgsAdmiss hr hRep hAs .nil
    simpa only [emptySubstitute,Conclusion] using h

#print axioms exact_WholeTupleSimulation

end LogicLineages.PersistentMarking.NumberedWindowTupleSplitChecks
