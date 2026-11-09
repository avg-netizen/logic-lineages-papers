module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformObjectPathDispatchSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformObjectPathDispatchProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformObjectPathDispatch InternalOriginalUniformObjectPathDispatchTargets
open InternalOriginalUniformObjectPathDispatchSupportProof
open InternalAcceptanceBranchProof InternalPositiveUnfoldingSupportProof

theorem actualInternalOriginalUniformObjectPathActiveGraph :
    ActualInternalOriginalUniformObjectPathActiveGraph := by
  intro window vertexProgram oldLift body α Delta context domain codomain gammaCode argumentObject argument parameter certificate out
  let a := activePremises window context gammaCode argumentObject argument parameter
  let g := dispatchGraph window vertexProgram oldLift out context domain codomain argumentObject certificate
  let f := InternalApplicationPathMap.mapGraph vertexProgram out certificate parameter domain codomain argument
  obtain ⟨hf⟩ := dispatchRecover (body := body) (Delta := g :: a :: Delta)
    window vertexProgram oldLift context domain codomain gammaCode argumentObject argument parameter certificate out
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := dispatchAccept (body := body) (Delta := f :: a :: Delta)
    window vertexProgram oldLift context domain codomain gammaCode argumentObject argument parameter certificate out
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem actualInternalOriginalUniformObjectPathZeroGraph :
    ActualInternalOriginalUniformObjectPathZeroGraph := by
  intro window vertexProgram oldLift body α Delta context domain codomain argumentObject certificate out
  obtain ⟨h⟩ := actualOriginalZeroBranch body 5 (windowTest window) oldLift (activeBranch vertexProgram)
    α out (arguments context domain codomain argumentObject certificate)
  exact ⟨weakenClosed h Delta⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformObjectPathDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformObjectPathDispatchProof
