module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningTargets
open UniformCertificateCompletion OriginalFinalVariableWeakening
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- All symbolic outputs, with only original pair/cons/constructor hypotheses. -/
def ActualOriginalFinalVariableSourceWeakening : Prop :=
  ∀ (guard : Program 1) (p : GlobalSourcePackage.Inputs), SourceLaw guard p

/-- Independent internal target weakening, not native semantic reflection. -/
def ActualOriginalFinalVariableTargetWeakening : Prop :=
  ∀ (guard : Program 1) (p : GlobalSourcePackage.Inputs), TargetLaw guard p

/-- One original selection retains the entire preceding package and both
new SAME-final internal laws, before every finite window and runtime Gamma. -/
def ActualOriginalFinalVariableWeakeningSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ (p : GlobalSourcePackage.Inputs) (guard : Program 1), Properties n arity p guard

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningTargets
