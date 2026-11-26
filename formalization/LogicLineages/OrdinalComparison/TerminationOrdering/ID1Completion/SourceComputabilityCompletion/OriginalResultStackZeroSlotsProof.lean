module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackZeroSlotsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackZeroSlotsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open InternalControlGraphSupportProof (projectionValue)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNe)
open OriginalTypedDecoderInternalBranchProof (sameNoIntro)
theorem actualZero : OriginalResultStackZeroSlotsTargets.ActualZero := by
 intro body alpha Delta count stack
 let xs : Fin 3 → OTerm alpha := ![z,count,stack]
 have hfirst : Nonempty (Derivation body Delta
   (graph3 OriginalHereditaryResultStackProgram.firstSlot z z count stack)) :=
  InternalAcceptanceBranchProof.zeroBranchIntro (.projection 0) (OriginalRawSyntaxTransport.constant 3 0) _
   z xs (projectionValue 0 xs) (constantValue 0 xs)
 have hsecond : Nonempty (Derivation body Delta
   (graph3 OriginalHereditaryResultStackProgram.secondSlot z z count stack)) :=
  sameNoIntro (.projection 0) (OriginalRawSyntaxTransport.constant 3 2) _ (OriginalRawSyntaxTransport.constant 3 0)
   z z (suc (suc z)) xs (projectionValue 0 xs) (constantValue 2 xs)
   (numeralNe 0 2 (by decide)) (constantValue 0 xs)
 obtain ⟨hf⟩ := hfirst
 obtain ⟨hs⟩ := hsecond
 exact ⟨Derivation.conjunctionIntroduction hf hs⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackZeroSlotsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackZeroSlotsProof
