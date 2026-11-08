module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalOriginalApplicationStep InternalApplicationStepPeelSupportProof

theorem actualOriginalGuardedApplicationStep :
    InternalOriginalApplicationStepTargets.ActualOriginalGuardedApplicationStep := by
  intro body data α arrow d e s t a k sourceApp targetApp liftedStep
  let premise := InternalOriginalApplicationStep.liftPremises data
    arrow d e s t a k sourceApp targetApp liftedStep ⊓ accepted data s t k
  have hp : Nonempty (Derivation body [premise] premise) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := InternalOriginalApplicationStepSupportProof.applicationStep data
    arrow d e s t a k sourceApp targetApp liftedStep (andLeft hp) (andRight hp)
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualOriginalSelectedApplicationStep :
    InternalOriginalApplicationStepTargets.ActualOriginalSelectedApplicationStep := by
  intro n arity symbols S Gamma table
  obtain ⟨data,h⟩ := InternalOriginalApplicationStepEvaluationProof.calibratedDataExists
    n arity symbols S Gamma table
  exact ⟨data,h,InternalOriginalApplicationStepEvaluationProof.selectedCalibration
    n arity symbols S Gamma table data h,
    fun body α arrow d e s t a k sourceApp targetApp liftedStep =>
      actualOriginalGuardedApplicationStep body data α
        arrow d e s t a k sourceApp targetApp liftedStep⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepProof
