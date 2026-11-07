module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationGuardedApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationGuardedProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open ApplicationGuarded ApplicationGuardedApplicationProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Extend the SAME previously constructed source/computability witnesses.
Only application changes; the old typed, ground and guard clauses are retained
by their literal definitions, not taken from unrelated existential witnesses. -/
theorem actualUniformApplicationClosureExists : ApplicationGuardedTargets.ActualUniformApplicationClosureExists := by
  intro n arity
  obtain ⟨src,old,hs,hc,hclosure,hguard⟩ := GammaGuardedSourceProof.actualUniformGuardClosureExists n arity
  obtain ⟨window,hw⟩ := GuardCalibrationProof.actualValidWindowProgram n
  obtain ⟨arrow,ha⟩ := Proof.allPrimitiveFunctions 2 ApplicationDomain.arrowValue
    ApplicationDomainProgramProof.arrowPrimitive
  obtain ⟨result,success,hr,_,_⟩ := ApplicationResultBuilderProof.actualProgramWitnesses n arity
  let comp := InternalApplication.computability old window arrow result
  have hcomp := InternalApplicationCalibrationProof.actualCalibration n arity old window arrow result hc hw ha hr
  refine ⟨src,comp,hs,hcomp,?_,?_⟩
  · intro symbols S table hclosed α
    let context := OrdinaryArithmeticQuotient.contextCode symbols S table
    have hwindow : evaluate window (List.Vector.ofFn ![context]) = 1 := by
      rw [hw]
      exact (GuardCalibrationProof.actualOriginalWindowCalibration n symbols S table).mpr hclosed
    have harrow (sigma tau : Ty) :
        evaluate arrow (List.Vector.ofFn ![typeNumber sigma,typeNumber tau]) = typeNumber (.arrow sigma tau) := by
      rw [ha]
      rfl
    obtain ⟨htyped,hground⟩ := hclosure symbols S table hclosed α
    refine ⟨htyped,hground,?_,?_⟩
    · intro sigma tau f a
      exact actualOriginalTotality (SourcePresentation.sourceBody src context) old window arrow result
        context sigma tau hwindow (harrow sigma tau) α f a
    · intro sigma tau f a out other
      exact actualOriginalFunctionality (SourcePresentation.sourceBody src context) old window arrow result
        context sigma tau hwindow (harrow sigma tau) α f a out other
  · exact hguard

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationGuardedProof
