module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.InductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z eqn suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114

open Targets
def fields {alpha : Type} (raw left right out : OTerm alpha) : Formula alpha :=
  lookupAgreement raw left right ⊓ graph2 ExchangeMapGraph.mapGraph out raw left
def result {alpha : Type} (raw left right out : OTerm alpha) : Formula alpha :=
  graph2 ExchangeMapGraph.mapGraph out raw right
def matrix {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  (fields (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).imp
    (result (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)))
def AtRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix raw)
def rawPredicate {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw (.var (.inr 0))
def BelowRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below rawPredicate raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.InductionDefinitions
