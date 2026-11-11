module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParameters
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Proof-side choice of the two modes with unused parameters. -/
def selectedMode (rank : Bool) : OriginalRawSyntaxTransport.Mode :=
  if rank then .rank else .shift

/-- Shift keeps its cutoff; rank permits a different cutoff as well. -/
def parameterMatrix {alpha : Type} (p : Program 3) (rank : Bool) (raw : OTerm alpha) :
    Formula (alpha ⊕ Fin 5) :=
  (graph3 p (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (raw.relabel Sum.inl)).imp
    (graph3 p (.var (.inr 0)) (.var (.inr 3))
      (if rank then .var (.inr 4) else .var (.inr 2)) (raw.relabel Sum.inl))

def AtRaw {alpha : Type} (p : Program 3) (rank : Bool) (raw : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (parameterMatrix p rank raw)

def rawPredicate {alpha : Type} (p : Program 3) (rank : Bool) : Formula (alpha ⊕ Fin 1) :=
  AtRaw p rank (.var (.inr 0))

def BelowRaw {alpha : Type} (p : Program 3) (rank : Bool) (raw : OTerm alpha) : Formula alpha :=
  InternalStrongInduction.below (rawPredicate p rank) raw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParameters
