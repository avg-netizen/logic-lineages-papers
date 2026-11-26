module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership

/-- An actual existential source vertex, not an external decoded witness. -/
def sourceWitness (E : Program 3) {alpha : Type} (reached candidate parameter : OTerm alpha) : Formula alpha :=
  existsOne (graph2 contains (numeral 1) (reached.relabel Sum.inl) (.var (.inr 0)) ⊓
    graph3 E (numeral 1) (.var (.inr 0)) (candidate.relabel Sum.inl) (parameter.relabel Sum.inl))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness
