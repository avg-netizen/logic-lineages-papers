module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionInductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedDirectBottomTrace

/-- Acceptance of an actual run at its original path and both actual states. -/
def fields {alpha : Type} (source : Program 2) (leaf : Program 4)
 (path out state : OTerm alpha) : Formula alpha :=
 InternalRawListRepeat.repeatGraph (transition source leaf) out path state ⊓
 graph1 (finish source leaf) (suc z) out

/-- The same path, initial state and final state under the destination leaf. -/
def result {alpha : Type} (source : Program 2) (leaf : Program 4)
 (path out state : OTerm alpha) : Formula alpha :=
 InternalRawListRepeat.repeatGraph (transition source leaf) out path state ⊓
 graph1 (finish source leaf) (suc z) out

/-- Both states are universally bound inside the arithmetic induction
hypothesis. Only the original path is the induction parameter. -/
def matrix {alpha : Type} (source : Program 2) (leaf outLeaf : Program 4)
 (path : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
 (fields source leaf (path.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))).imp
 (result source outLeaf (path.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)))

def AtPath {alpha : Type} (source : Program 2) (leaf outLeaf : Program 4)
 (path : OTerm alpha) : Formula alpha :=
 InternalClosedPrograms.allBlock (matrix source leaf outLeaf path)

def pathPredicate {alpha : Type} (source : Program 2) (leaf outLeaf : Program 4) :
 Formula (alpha ⊕ Fin 1) :=
 AtPath source leaf outLeaf (.var (.inr 0))

def BelowPath {alpha : Type} (source : Program 2) (leaf outLeaf : Program 4)
 (path : OTerm alpha) : Formula alpha :=
 InternalStrongInduction.below (pathPredicate source leaf outLeaf) path
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionInductionDefinitions
