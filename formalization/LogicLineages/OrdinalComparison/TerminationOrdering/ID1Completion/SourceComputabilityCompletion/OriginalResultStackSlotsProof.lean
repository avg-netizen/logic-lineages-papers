module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSupportProof
open InternalArithmeticProgramsSupportProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNe)
open OriginalTypedDecoderInternalBranchProof (sameYesIntro sameNoIntro)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalResultStackSlotsSupportProof OriginalResultStackSlotsBoundaryProof

theorem oneChild : OriginalResultStackSlotsTargets.OneChild := by
 intro body alpha Delta count initialList suffix joined value old hl ha hc
 have hlookup := boundary body alpha Delta count initialList suffix joined value hl ha
   (InternalRawListRecursionSupportProof.consHead suffix value old hc)
 exact InternalApplicationStepPeelSupportProof.andIntro
   (firstAt z count joined (suc count) count value (additionOne count)
     (InternalEqualityTestPredecessorProof.predecessorSuccessor count) hlookup)
   (secondOne count joined)

theorem twoChildren : OriginalResultStackSlotsTargets.TwoChildren := by
 intro body alpha Delta count initialList suffix joined first second tail old hl ha hc ht
 have hsecond := boundary body alpha Delta count initialList suffix joined second hl ha
   (InternalRawListRecursionSupportProof.consHead suffix second tail hc)
 have hfirst := nextBoundary count initialList suffix joined tail first hl ha
   (InternalRawListRecursionSupportProof.consTail suffix second tail hc)
   (InternalRawListRecursionSupportProof.consHead tail first old ht)
 exact InternalApplicationStepPeelSupportProof.andIntro
   (firstAt (suc z) count joined (suc (suc count)) (suc count) first (additionTwo count)
     (InternalEqualityTestPredecessorProof.predecessorSuccessor (suc count)) hfirst)
   (secondTwo count joined second hsecond)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsProof
