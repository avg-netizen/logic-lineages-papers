import LogicLineages.PersistentMarking.ProtectedSpineApplicationGapOldProof

namespace LogicLineages.PersistentMarking.ProtectedSpineApplicationGapChecks
open Spine DecisionInventory DecisionPorts HereditaryDomainSemantics
open ProtectedSpineLaws ProtectedSpineInterpreter
open ProtectedSpineApplicationCounterexampleTargets ProtectedSpineApplicationGapInputs

theorem resultCovered : Covered inputEnvironment sourceHeads result := by
  constructor
  · intro σ h
    simp [result,arguments,argument,auxiliarySupport,auxiliaryArgs,declaration,Head.result,Head.arguments,TypeSupport.subtypes] at h
    rcases h with (rfl | rfl)
    · decide
    · decide
  · intro f h
    simp [result,arguments,argument,heads,headsArgs] at h
    subst f
    exact List.mem_cons_self

theorem resultAvailable (S : Signature) :
    (decode inputEnvironment .ground context (interpreted S result)).available context = true := by
  have hty : Typed EmptyContext result .ground := .marked .nil (.cons .free .nil)
  have hp := MarkedConstructorInventoryProof.prefixClosed source target _ _
    (sourcePaper S).1 (targetPaper S).1 sourceOrdinary targetOrdinary
  have hl := ProtectedSpineInterpretationProof.laws S inputEnvironment sourceHeads bottomFamily hp bottomRetained
    EmptyContext result .ground hty resultCovered
  have h := (ProtectedSpineEncodingProof.encodeAt inputEnvironment .ground
    (evaluate S inputEnvironment sourceHeads bottomFamily result) hl context ⟨[],[]⟩ initialAssignments).2
  exact (h context contextValid (DecisionPortsProof.extensionRefl context)).1

theorem exact_AvailabilityGap : AvailabilityGap := by
  intro S
  have ha := ProtectedSpineApplicationGapOldProof.helperUnavailable S
  have hb := resultAvailable S
  refine ⟨sourcePaper S,sourceOrdinary,targetPaper S,targetOrdinary,contextValid,bottomRetained,callTyped,
    application,ha,hb,?_⟩
  intro he
  rw [he,hb] at ha
  cases ha

#print axioms exact_AvailabilityGap
end LogicLineages.PersistentMarking.ProtectedSpineApplicationGapChecks
