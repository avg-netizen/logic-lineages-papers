module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredTermReturnTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackDeletionRowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackOldSuffixProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackZeroSlotsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalTermProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredTermReturnProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalOriginalUniformVertexPathSupportProof (ternaryValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem selected (P : Program 3) (input children count results out : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.childCount children input)))
 (hd : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.deletionCount count input)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.results results input)))
 (hv : Nonempty (Derivation body Delta (graph3 P out children count results))) :
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.selected P) out input)) :=
 ternaryValue P OriginalHereditaryReturnStep.childCount OriginalHereditaryReturnStep.deletionCount
  OriginalHereditaryReturnStep.results out children count results ![input] hv hc hd hr
theorem children0 : OriginalRestoredTermReturnTargets.Children0 := by
 intro R body alpha Delta input work results frame rest payload packed parameter count row reversed old root returned tail value stack out
  hstate hwork hframe hrole hpacked hparameter hchildren hcount hlength hreverse happend hroot hreturned htail hvalue hstack hout
 have hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.results results input)) :=
  unaryValue InternalUnpair.right (.projection 0) results input ![input] (pairRight input work results hstate) (projectionValue 0 ![input])
 obtain ⟨laws⟩ := OriginalReverseLengthInvolutionProof.actualLaws body alpha Delta row count reversed hlength hreverse
 obtain ⟨slots⟩ := OriginalResultStackZeroSlotsProof.actualZero body alpha Delta count results
 have hrow := OriginalResultStackDeletionRowProof.actualRestoration body alpha Delta z count row reversed old results hlength hreverse happend
 have hold := OriginalResultStackOldSuffixProof.children0 body alpha Delta count row reversed old results hlength hreverse happend
 exact OriginalHereditaryReturnStepInternalTermProof.termLaw R body alpha Delta
  input work results frame rest payload packed parameter z z row old root returned tail value stack out
  hstate hwork hframe hrole hpacked hparameter
  (selected OriginalHereditaryResultStackProgram.firstSlot input z count results z hchildren hcount hr ⟨Derivation.conjunctionLeft slots⟩)
  (selected OriginalHereditaryResultStackProgram.secondSlot input z count results z hchildren hcount hr ⟨Derivation.conjunctionRight slots⟩)
  (selected OriginalHereditaryResultStackProgram.deletionRow input z count results row hchildren hcount hr hrow)
  (selected OriginalHereditaryResultStackProgram.oldSuffix input z count results old hchildren hcount hr hold)
  hroot hreturned htail hvalue hstack hout
theorem children1 : OriginalRestoredTermReturnTargets.Children1 := by
 intro R body alpha Delta input work results frame rest payload packed parameter count row reversed old root returned tail value stack out suffix first
  hstate hwork hframe hrole hpacked hparameter hchildren hcount hlength hreverse happend hc1 hroot hreturned htail hvalue hstack hout
 have hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.results results input)) :=
  unaryValue InternalUnpair.right (.projection 0) results input ![input] (pairRight input work results hstate) (projectionValue 0 ![input])
 obtain ⟨laws⟩ := OriginalReverseLengthInvolutionProof.actualLaws body alpha Delta row count reversed hlength hreverse
 obtain ⟨slots⟩ := OriginalResultStackSlotsProof.oneChild body alpha Delta count reversed suffix results first old ⟨Derivation.conjunctionLeft laws⟩ happend hc1
 have hrow := OriginalResultStackDeletionRowProof.actualRestoration body alpha Delta (suc z) count row reversed suffix results hlength hreverse happend
 have hold := OriginalResultStackOldSuffixProof.children1 body alpha Delta count row reversed old results suffix first hlength hreverse happend hc1
 exact OriginalHereditaryReturnStepInternalTermProof.termLaw R body alpha Delta
  input work results frame rest payload packed parameter first z row old root returned tail value stack out
  hstate hwork hframe hrole hpacked hparameter
  (selected OriginalHereditaryResultStackProgram.firstSlot input (suc z) count results first hchildren hcount hr ⟨Derivation.conjunctionLeft slots⟩)
  (selected OriginalHereditaryResultStackProgram.secondSlot input (suc z) count results z hchildren hcount hr ⟨Derivation.conjunctionRight slots⟩)
  (selected OriginalHereditaryResultStackProgram.deletionRow input (suc z) count results row hchildren hcount hr hrow)
  (selected OriginalHereditaryResultStackProgram.oldSuffix input (suc z) count results old hchildren hcount hr hold)
  hroot hreturned htail hvalue hstack hout
theorem children2 : OriginalRestoredTermReturnTargets.Children2 := by
 intro R body alpha Delta input work results frame rest payload packed parameter count row reversed old root returned tail value stack out suffix childTail first second
  hstate hwork hframe hrole hpacked hparameter hchildren hcount hlength hreverse happend hc1 hc2 hroot hreturned htail hvalue hstack hout
 have hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.results results input)) :=
  unaryValue InternalUnpair.right (.projection 0) results input ![input] (pairRight input work results hstate) (projectionValue 0 ![input])
 obtain ⟨laws⟩ := OriginalReverseLengthInvolutionProof.actualLaws body alpha Delta row count reversed hlength hreverse
 obtain ⟨slots⟩ := OriginalResultStackSlotsProof.twoChildren body alpha Delta count reversed suffix results first second childTail old ⟨Derivation.conjunctionLeft laws⟩ happend hc1 hc2
 have hrow := OriginalResultStackDeletionRowProof.actualRestoration body alpha Delta (suc (suc z)) count row reversed suffix results hlength hreverse happend
 have hold := OriginalResultStackOldSuffixProof.children2 body alpha Delta count row reversed old results suffix childTail first second hlength hreverse happend hc1 hc2
 exact OriginalHereditaryReturnStepInternalTermProof.termLaw R body alpha Delta
  input work results frame rest payload packed parameter first second row old root returned tail value stack out
  hstate hwork hframe hrole hpacked hparameter
  (selected OriginalHereditaryResultStackProgram.firstSlot input (suc (suc z)) count results first hchildren hcount hr ⟨Derivation.conjunctionLeft slots⟩)
  (selected OriginalHereditaryResultStackProgram.secondSlot input (suc (suc z)) count results second hchildren hcount hr ⟨Derivation.conjunctionRight slots⟩)
  (selected OriginalHereditaryResultStackProgram.deletionRow input (suc (suc z)) count results row hchildren hcount hr hrow)
  (selected OriginalHereditaryResultStackProgram.oldSuffix input (suc (suc z)) count results old hchildren hcount hr hold)
  hroot hreturned htail hvalue hstack hout
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredTermReturnProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredTermReturnProof
