module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.InductionDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.InductionDefinitions
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
def fields (D : Program 2) (G : Program 3) (raw query old param deps answers value out : OTerm alpha) : Formula alpha :=
  graph2 contains (numeral 1) raw query ⊓
  (graph2 D deps query param ⊓
  (graph2 ExchangeMapGraph.mapGraph answers deps old ⊓
  (graph3 G (suc value) query answers param ⊓
   graph3 (ExchangeGraphStage.stage D G) out raw old param)))
def result (query value out : OTerm alpha) : Formula alpha := graph2 ExchangeMapGraph.lookup (suc value) out query
def matrix (D : Program 2) (G : Program 3) (raw : OTerm alpha) : Formula (alpha ⊕ Fin 7) :=
  (fields D G (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6))).imp
    (result (.var (.inr 0)) (.var (.inr 5)) (.var (.inr 6)))
def AtRaw (D : Program 2) (G : Program 3) (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix D G raw)
def rawPredicate (D : Program 2) (G : Program 3) : Formula (alpha ⊕ Fin 1) := AtRaw D G (.var (.inr 0))
def BelowRaw (D : Program 2) (G : Program 3) (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below (rawPredicate D G) raw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.InductionDefinitions
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.InductionDefinitions
