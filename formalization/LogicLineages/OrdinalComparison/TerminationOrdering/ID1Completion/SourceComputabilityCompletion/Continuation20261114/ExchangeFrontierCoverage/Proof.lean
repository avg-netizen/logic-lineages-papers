module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierCoverage.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierCoverage.Proof
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
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof
open RawHeadWindowCoverage.RelationFoldCoreProof
open GuardedSourceSyntaxProof (numeralRename)

theorem flattenCoverage : Targets.InternalFlattenCoverage := by
  intro body alpha Delta D frontier node param deps child out hm hd hc hf
  exact RawHeadWindowCoverage.RelationFoldProof.coverage (InternalAcceptance.constantZero 1)
    (ExchangeFrontier.flattenStep D) (dependencyMember D) (SupportProof.hit D) (SupportProof.keep D)
    frontier node child out (Fin.cons param Fin.elim0) (SupportProof.observe D node param deps child hd hc) hm hf

theorem successorCoverage : Targets.InternalSuccessorCoverage := by
  intro body alpha Delta D depth seed param frontier node deps child out hf hm hd hc ho
  have hflat := (ExchangeFrontier.InternalProof.internalBindSuccessor body alpha Delta D depth seed param frontier out hf).mp ho
  exact flattenCoverage body alpha Delta D frontier node param deps child out hm hd hc hflat

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierCoverage.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierCoverage.Proof
