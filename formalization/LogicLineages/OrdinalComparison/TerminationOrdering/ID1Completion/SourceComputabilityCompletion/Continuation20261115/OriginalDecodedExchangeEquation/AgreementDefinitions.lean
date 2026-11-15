module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.AgreementDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Private induction premise, later built from actual predecessor coverage. -/
def agreementMatrix (E : Program 2) {alpha : Type} (keys left right : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  (graph2 contains (numeral 1) (keys.relabel Sum.inl) (.var (.inr 0))).imp
    ((graph2 E (.var (.inr 1)) (.var (.inr 0)) (left.relabel Sum.inl)).imp
      (graph2 ExchangeMapGraph.lookup (suc (.var (.inr 1))) (right.relabel Sum.inl) (.var (.inr 0))))
def lookupAgreement (E : Program 2) {alpha : Type} (keys left right : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (agreementMatrix E keys left right)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.AgreementDefinitions
