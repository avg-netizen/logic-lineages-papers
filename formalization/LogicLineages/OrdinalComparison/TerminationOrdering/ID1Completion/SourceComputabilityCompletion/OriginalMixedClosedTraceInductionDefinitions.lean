module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceInductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def fields {alpha : Type} (source : Program 2) (leaf : Program 4)
 (path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha) : Formula alpha :=
 graph1 InternalUnpair.left path cert ⊓
 (graph2 source (numeral 1) s oldParam ⊓
 (graph4 leaf (numeral 1) s t cert oldParam ⊓
 (graph4 (OriginalMixedDirectBottomTrace.recognizes source leaf) (numeral 1) s t cert oldParam ⊓
 (OriginalContextInsertion.Insert d cutoff gamma extended ⊓
 (graph2 InternalPairing.pairing oldParam c extended ⊓
 (graph2 InternalPairing.pairing newParam c gamma ⊓
 (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓
  graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t)))))))

def result {alpha : Type} (source : Program 2) (leaf : Program 4)
 (s t newParam erasedS erasedT : OTerm alpha) : Formula alpha :=
 graph2 source (numeral 1) erasedS newParam ⊓
 OriginalExistentialRankResultDefinitions.Result leaf erasedS erasedT newParam s t

/-- Every endpoint, certificate, runtime context and cutoff is under the
internal IH. The only externally fixed arithmetic term is the original path. -/
def matrix {alpha : Type} (source : Program 2) (leaf outLeaf : Program 4)
 (path : OTerm alpha) : Formula (alpha ⊕ Fin 12) :=
 (fields source leaf (path.relabel Sum.inl)
  (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))
  (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6)) (.var (.inr 7))
  (.var (.inr 8)) (.var (.inr 9)) (.var (.inr 10)) (.var (.inr 11))).imp
 (result source outLeaf (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 4)) (.var (.inr 10)) (.var (.inr 11)))

def AtPath {alpha : Type} (source : Program 2) (leaf outLeaf : Program 4) (path : OTerm alpha) : Formula alpha :=
 InternalClosedPrograms.allBlock (matrix source leaf outLeaf path)
def pathPredicate {alpha : Type} (source : Program 2) (leaf outLeaf : Program 4) : Formula (alpha ⊕ Fin 1) :=
 AtPath source leaf outLeaf (.var (.inr 0))
def BelowPath {alpha : Type} (source : Program 2) (leaf outLeaf : Program 4) (path : OTerm alpha) : Formula alpha :=
 InternalStrongInduction.below (pathPredicate source leaf outLeaf) path
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceInductionDefinitions
