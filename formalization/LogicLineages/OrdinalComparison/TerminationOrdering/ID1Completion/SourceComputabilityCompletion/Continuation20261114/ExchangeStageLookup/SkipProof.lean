module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.SkipProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel eqnRelabel)
theorem skippedLookup : Targets.InternalSkippedLookup := by
  intro body alpha Delta D G frontier node tail old param deps answers out rest key result hf hd hm hg ho hr
  have ht := (ExchangeGraphStage.InternalProof.internalSkip body alpha Delta D G
    frontier node tail old param deps answers out hf hd hm hg).mp ho
  have he := valueUnique (ExchangeGraphStage.stage D G) out rest ![tail,old,param] ht hr
  constructor
  · intro h
    exact headTransport ExchangeMapGraph.lookup result out rest (Fin.cons key Fin.elim0) he h
  · intro h
    obtain ⟨e⟩ := he
    exact headTransport ExchangeMapGraph.lookup result rest out (Fin.cons key Fin.elim0) ⟨symm e⟩ h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.SkipProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.SkipProof
