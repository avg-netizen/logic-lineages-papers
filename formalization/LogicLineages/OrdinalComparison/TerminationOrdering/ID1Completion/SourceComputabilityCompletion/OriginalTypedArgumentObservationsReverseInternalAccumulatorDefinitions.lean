module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalTerminationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalClosedPrograms
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalTypedArgumentObservations OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Proof auxiliary only: exactly the existing reverse loop with arbitrary
initial accumulator. The original reverse and all runtime tuples are unchanged. -/
def initial : Program 2 := pairOf (.projection 0) (.projection 1)
def run : Program 2 := .composition reverseRun ![succOf (.projection 0),initial]
def accumulated : Program 2 := rightOf run

def fields {alpha : Type} (front value singleton combined acc left right : OTerm alpha) : Formula alpha :=
 graph2 InternalListCodec.consCode singleton value z ⊓
 (graph2 InternalApplicationValidityStackAppend.append combined front singleton ⊓
 (graph2 accumulated left front acc ⊓ graph2 accumulated right combined acc))
def matrix {alpha : Type} (front : OTerm alpha) : Formula (alpha ⊕ Fin 6) :=
 (fields (front.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
   (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5))).imp
 (graph2 InternalListCodec.consCode (.var (.inr 5)) (.var (.inr 0)) (.var (.inr 4)))
def AtRaw {alpha : Type} (front : OTerm alpha) : Formula alpha := allBlock (matrix front)
def rawPredicate {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw (.var (.inr 0))
def BelowRaw {alpha : Type} (front : OTerm alpha) : Formula alpha := InternalStrongInduction.below rawPredicate front
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorDefinitions
