module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def fields {alpha : Type} (input d k out before after : OTerm alpha) : Formula alpha :=
  graph3 OriginalRawSyntaxTransport.eraseRaw out d k input ⊓
    (graph1 OriginalStructuralNodeSize.raw before input ⊓ graph1 OriginalStructuralNodeSize.raw after out)
def matrix {alpha : Type} (input : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
  (fields (input.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
    (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4))).imp
      (equal (.var (.inr 3)) (.var (.inr 4)))
def AtRaw {alpha : Type} (input : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (matrix input)
def rawPredicate {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw (.var (.inr 0))
def BelowRaw {alpha : Type} (input : OTerm alpha) : Formula alpha :=
  InternalStrongInduction.below rawPredicate input

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureDefinitions
