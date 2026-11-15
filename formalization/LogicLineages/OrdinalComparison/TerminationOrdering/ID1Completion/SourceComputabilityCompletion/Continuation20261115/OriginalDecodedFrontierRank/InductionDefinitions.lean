module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.InductionDefinitions
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
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def result (depth seed child : OTerm alpha) : Formula alpha :=
  PrimaryUncoveredCount.bounded (OrdinaryArithmetic.addTerm depth child) seed
def fields (n : Nat) (depth seed param frontier child seedRank childRank : OTerm alpha) : Formula alpha :=
  (graph2 (OriginalDecodedRank.rank n) seedRank seed param ⊓
   graph3 (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) frontier depth seed param) ⊓
  (graph2 contains (numeral 1) frontier child ⊓ graph2 (OriginalDecodedRank.rank n) childRank child param)
def matrix (n : Nat) (depth : OTerm alpha) : Formula (alpha ⊕ Fin 6) :=
  (fields n (depth.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))
    (.var (.inr 4)) (.var (.inr 5))).imp
    (result (depth.relabel Sum.inl) (.var (.inr 4)) (.var (.inr 5)))
def AtCount (n : Nat) (depth : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix n depth)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.InductionDefinitions
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.InductionDefinitions
