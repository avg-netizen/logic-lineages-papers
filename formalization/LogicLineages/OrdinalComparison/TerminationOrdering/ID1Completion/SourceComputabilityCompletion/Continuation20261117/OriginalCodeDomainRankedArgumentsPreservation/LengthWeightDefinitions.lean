module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.FoldDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeight
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport
/-- Each actual extracted entry contributes the original bound pair (1,0). -/
def weight : Program 1 := pairOf (constant 1 1) (constant 1 0)
def fields {alpha : Type} (raw count out : OTerm alpha) : Formula alpha :=
  graph1 OriginalContextInsertion.length count raw ⊓ graph2 InternalPairing.pairing out count z
def result {alpha : Type} (raw out : OTerm alpha) : Formula alpha := graph1 (Auxiliary.Fold.weighted weight) out raw
def matrix {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  let x : Fin 2 → OTerm (alpha ⊕ Fin 2) := fun i => .var (.inr i)
  (fields (raw.relabel Sum.inl) (x 0) (x 1)).imp (result (raw.relabel Sum.inl) (x 1))
def AtRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix raw)
def predicate {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw (.var (.inr 0))
def BelowRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below predicate raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeight
