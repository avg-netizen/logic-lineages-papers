module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellation
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Proof-side right inverse at a raw input. The shift fold uses its literal
public erased-type argument zero; the erasure's type and cutoff remain bound. -/
def cancellationMatrix {alpha : Type} (p q : Program 3) (raw : OTerm alpha) :
    Formula (alpha ⊕ Fin 3) :=
  (graph3 p (.var (.inr 2)) (numeral 0) (.var (.inr 1)) (raw.relabel Sum.inl)).imp
    (graph3 q (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)))

def AtRaw {alpha : Type} (p q : Program 3) (raw : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (cancellationMatrix p q raw)

def rawPredicate {alpha : Type} (p q : Program 3) : Formula (alpha ⊕ Fin 1) :=
  AtRaw p q (.var (.inr 0))

def BelowRaw {alpha : Type} (p q : Program 3) (raw : OTerm alpha) : Formula alpha :=
  InternalStrongInduction.below (rawPredicate p q) raw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellation
