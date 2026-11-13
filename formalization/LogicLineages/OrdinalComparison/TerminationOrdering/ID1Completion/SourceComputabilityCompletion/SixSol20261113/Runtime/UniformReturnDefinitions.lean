module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalClosedPrograms (allBlock)
open InternalFiniteBlocks (block)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (suc)
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual return geometry after child visits. `produced` is the complete
stack-order row, with the original old results appended behind it. -/
def geometry {alpha : Type}
 (frame produced value suffix old work results input pushed output : OTerm alpha) : Formula alpha :=
 graph2 InternalListCodec.consCode work frame suffix ⊓
 (graph2 InternalApplicationValidityStackAppend.append results produced old ⊓
 (graph2 InternalPairing.pairing input work results ⊓
 (graph2 InternalListCodec.consCode pushed value old ⊓
  graph2 InternalPairing.pairing output suffix pushed)))
def frameBody {alpha : Type} (R : Program 2) (frame produced value : OTerm alpha) : Formula (alpha ⊕ Fin 7) :=
 (geometry (frame.relabel Sum.inl) (produced.relabel Sum.inl) (value.relabel Sum.inl)
   (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))
   (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6))).imp
 (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) (.var (.inr 6))
   (suc (numeral 0)) (.var (.inr 4)))
def Framed {alpha : Type} (R : Program 2) (frame produced value : OTerm alpha) : Formula alpha :=
 allBlock (frameBody R frame produced value)
def matrix {alpha : Type} (R : Program 2) (frame produced : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
 Framed R (frame.relabel Sum.inl) (produced.relabel Sum.inl) (.var (.inr 0))
/-- One returned value precedes all arbitrary agenda and result backgrounds.
The old suffix is restored literally, not merely up to its length. -/
def Completion {alpha : Type} (R : Program 2) (frame produced : OTerm alpha) : Formula alpha :=
 block (matrix R frame produced)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnDefinitions
