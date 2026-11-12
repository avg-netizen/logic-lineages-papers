module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Existential ORIGINAL endpoint ranks; no transformed rank or observer
rank is substituted. The inner binder is the after-rank. -/
def AfterMatrix {alpha : Type} (oldS oldT before : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
 OriginalLambdaOriginalRankDefinitions.PackedRankDrop (oldS.relabel Sum.inl) (oldT.relabel Sum.inl)
   (before.relabel Sum.inl) (.var (.inr 0))
def AfterWitness {alpha : Type} (oldS oldT before : OTerm alpha) : Formula alpha :=
 existsOne (AfterMatrix oldS oldT before)
def BeforeMatrix {alpha : Type} (oldS oldT : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
 AfterWitness (oldS.relabel Sum.inl) (oldT.relabel Sum.inl) (.var (.inr 0))
def RankWitness {alpha : Type} (oldS oldT : OTerm alpha) : Formula alpha :=
 existsOne (BeforeMatrix oldS oldT)
def Result {alpha : Type} (leaf : Program 4) (s t parameter oldS oldT : OTerm alpha) : Formula alpha :=
 (equal s t ⊓ RankWitness oldS oldT) ⊔ OriginalLambdaErasureSquareDichotomyDefinitions.Witness leaf s t parameter

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultDefinitions
