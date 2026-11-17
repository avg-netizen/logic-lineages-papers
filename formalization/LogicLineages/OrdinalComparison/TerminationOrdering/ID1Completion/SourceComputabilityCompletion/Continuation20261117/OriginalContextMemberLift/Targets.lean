module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalContextMemberLift.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalContextMemberLift.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- All outputs, no calibration or supplied internal graph-equivalence premise. -/
def InternalContextMemberLift : Prop := ∀ (M : Program 2) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (out typ context : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 (InternalOriginalUniformContextMembership.contextMember (liftMember M)) out typ context).iff
      (graph2 M out typ context)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalContextMemberLift.Targets
