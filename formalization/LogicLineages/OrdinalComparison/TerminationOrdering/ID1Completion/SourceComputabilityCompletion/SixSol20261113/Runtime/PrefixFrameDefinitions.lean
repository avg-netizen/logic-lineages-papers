module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.FramedCompletionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalClosedPrograms (allBlock)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- All lists/states are actual numeric codec graphs. `produced` is in stack
order, so later execution puts its produced row before the earlier row. -/
def geometry {alpha : Type}
 (prefix produced suffix old work input joined output : OTerm alpha) : Formula alpha :=
 graph2 InternalApplicationValidityStackAppend.append work prefix suffix ⊓
 (graph2 InternalPairing.pairing input work old ⊓
 (graph2 InternalApplicationValidityStackAppend.append joined produced old ⊓
  graph2 InternalPairing.pairing output suffix joined))
def frameBody {alpha : Type} (R : Program 2)
 (prefix count produced : OTerm alpha) : Formula (alpha ⊕ Fin 6) :=
 (geometry (prefix.relabel Sum.inl) (produced.relabel Sum.inl)
   (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
   (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5))).imp
 (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) (.var (.inr 5))
   (count.relabel Sum.inl) (.var (.inr 3)))
/-- Count and produced row are outside every arbitrary agenda/result background.
This is a literal run specification, not admission or native evaluation. -/
def PrefixFrame {alpha : Type} (R : Program 2)
 (prefix count produced : OTerm alpha) : Formula alpha := allBlock (frameBody R prefix count produced)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameDefinitions
