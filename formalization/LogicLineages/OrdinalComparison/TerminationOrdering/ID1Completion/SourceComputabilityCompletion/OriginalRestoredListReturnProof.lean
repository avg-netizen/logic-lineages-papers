module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredListReturnTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredTermReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalListNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalListConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredListReturnProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalRestoredTermReturnProof (selected)
theorem listNil : OriginalRestoredListReturnTargets.Nil := by
 intro R body alpha Delta input work results frame rest payload raw rawPayload count row reversed old stack out
  hstate hwork hframe hrole hraw htag hchildren hcount hlength hreverse happend hstack hout
 have hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.results results input)) :=
  unaryValue InternalUnpair.right (.projection 0) results input ![input] (pairRight input work results hstate) (projectionValue 0 ![input])
 have hold := OriginalResultStackOldSuffixProof.children0 body alpha Delta count row reversed old results hlength hreverse happend
 exact OriginalHereditaryReturnStepInternalListNilProof.listNilLaw R body alpha Delta
  input work results frame rest payload raw rawPayload old stack out
  hstate hwork hframe hrole hraw htag
  (selected OriginalHereditaryResultStackProgram.oldSuffix input z count results old hchildren hcount hr hold) hstack hout
theorem listCons : OriginalRestoredListReturnTargets.Cons := by
 intro R body alpha Delta input work results frame rest payload raw rawPayload count row reversed old stack out suffix childTail first second value
  hstate hwork hframe hrole hraw htag hchildren hcount hlength hreverse happend hc1 hc2 hvalue hstack hout
 have hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.results results input)) :=
  unaryValue InternalUnpair.right (.projection 0) results input ![input] (pairRight input work results hstate) (projectionValue 0 ![input])
 obtain ⟨laws⟩ := OriginalReverseLengthInvolutionProof.actualLaws body alpha Delta row count reversed hlength hreverse
 obtain ⟨slots⟩ := OriginalResultStackSlotsProof.twoChildren body alpha Delta count reversed suffix results first second childTail old ⟨Derivation.conjunctionLeft laws⟩ happend hc1 hc2
 have hold := OriginalResultStackOldSuffixProof.children2 body alpha Delta count row reversed old results suffix childTail first second hlength hreverse happend hc1 hc2
 exact OriginalHereditaryReturnStepInternalListConsProof.listConsLaw R body alpha Delta
  input work results frame rest payload raw rawPayload first second old value stack out
  hstate hwork hframe hrole hraw htag
  (selected OriginalHereditaryResultStackProgram.firstSlot input (suc (suc z)) count results first hchildren hcount hr ⟨Derivation.conjunctionLeft slots⟩)
  (selected OriginalHereditaryResultStackProgram.secondSlot input (suc (suc z)) count results second hchildren hcount hr ⟨Derivation.conjunctionRight slots⟩)
  (selected OriginalHereditaryResultStackProgram.oldSuffix input (suc (suc z)) count results old hchildren hcount hr hold)
  hvalue hstack hout
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredListReturnProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredListReturnProof
