module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.InductionDefinitions
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

def result (depth seed child : OTerm alpha) : Formula alpha :=
  PrimaryUncoveredCount.bounded (OrdinaryArithmetic.addTerm depth child) seed
def fields (depth seed param frontier child : OTerm alpha) : Formula alpha :=
  graph3 (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency) frontier depth seed param ⊓
  graph2 contains (numeral 1) frontier child
def matrix (depth : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  (fields (depth.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))).imp
    (result (depth.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 3)))
def AtCount (depth : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix depth)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.InductionDefinitions
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.InductionDefinitions
