module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationDomainProgramProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCalibrationProof
open InternalApplication InternalAcceptanceCalibrationProof GuardedSourceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem vectorSix (v : List.Vector Nat 6) :
    List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,v.get 3,v.get 4,v.get 5] = v := by
  apply List.Vector.ext
  intro i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)))))) i

theorem evaluateFirstFive (p : Program 5) (v : List.Vector Nat 6) :
    evaluate (firstFive p) v = evaluate p (List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,v.get 3,v.get 4]) := by
  change evaluate p _ = evaluate p _
  congr 1

theorem evaluateResultCheck (result : Program 5) (v : List.Vector Nat 6) :
    evaluate (resultCheck result) v =
      if v.get 5 = evaluate result (List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,v.get 3,v.get 4]) then 1 else 0 := by
  rw [resultCheck,evalComposeTwo,evaluateFirstFive,evalEquality]
  rfl

theorem actualCalibration : InternalApplicationTargets.ActualCalibration := by
  intro n arity old window arrow result hc hw ha hr
  refine ⟨hc.1,hc.2.1,?_⟩
  intro v
  change evaluate (application (ApplicationDomain.activation window old.typed old.guard arrow)
    result old.application) v = _
  rw [application,evalBranch,evaluateFirstFive,
    ApplicationDomainProgramProof.actualExplicitActivation n arity window old.typed old.guard arrow
      hw hc.1 hc.2.1 ha]
  let w := List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,v.get 3,v.get 4]
  by_cases h : ApplicationDomain.active n arity w
  · dsimp only [w] at h
    have hs := (ApplicationDomainProof.actualDomainSuccess n arity
      (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4) h).2.1
    have hv := ApplicationResultBuilderProof.actualOriginalValue n arity
      (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4) (v.get 5)
    rw [vectorSix] at hv
    simp only [ApplicationDomain.activationValue,if_pos h,show (1 : Nat) ≠ 0 by decide,if_false]
    rw [evaluateResultCheck,hr,hv]
    simp only [hs,true_and]
  · dsimp only [w] at h
    simp only [ApplicationDomain.activationValue,if_neg h,if_pos rfl]
    exact hc.2.2 v

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCalibrationProof
