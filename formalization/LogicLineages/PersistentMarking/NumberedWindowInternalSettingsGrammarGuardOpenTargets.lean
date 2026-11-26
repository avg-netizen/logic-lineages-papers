module

public import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardOpenTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSettingsGrammarGuardDefinitions

/-- The rule is only for the literal reselected guard on its actual tape.
It gives both the unchanged original guard graph and the physical grammar
type occurrence. No corresponding rule for an arbitrary old T is assumed. -/
def ExactOpenSettingsRefitGuardReports : Prop :=
  ∀ (s : Settings) (T : Program 1)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ty : OTerm α),
    let source := unary (refitGuard s T) (suc z) ty
    let reports := unary T (suc z) ty ⊓
      memberGraph (numeral (Encodable.encode s.types)) ty
    Nonempty (Derivation body Γ ((source.imp reports) ⊓ (reports.imp source)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardOpenTargets
