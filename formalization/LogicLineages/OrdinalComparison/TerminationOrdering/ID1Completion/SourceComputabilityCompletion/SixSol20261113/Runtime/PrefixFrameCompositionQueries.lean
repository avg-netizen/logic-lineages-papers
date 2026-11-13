module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameCompositionCore
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.AppendReassociationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameCompositionQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename conjunctionRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PrefixFrameDefinitions PrefixFrameSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalOriginalOrderSyntaxProof (addRelabel)
theorem withMiddle (R : Program 2)
 (first second firstCount secondCount firstRow secondRow agendaPrefix produced suffix old work input joined output middleWork middleResults : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (PrefixFrame R first firstCount firstRow)))
 (hs : Nonempty (Derivation body Delta (PrefixFrame R second secondCount secondRow)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append agendaPrefix first second)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced secondRow firstRow)))
 (hg : Nonempty (Derivation body Delta (geometry agendaPrefix produced suffix old work input joined output)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append middleWork second suffix)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append middleResults firstRow old)))
 : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output (add firstCount secondCount) input)) := by
 apply programCases InternalPairing.pairing (Fin.cons middleWork (Fin.cons middleResults Fin.elim0)) _
 intro beta j Theta middle hinc hq
 simp only [graph2Rename,addRelabel]
 simp only [consTermRename,emptyRename] at hq
 have hf' := renameInto hf j Theta hinc
 have hs' := renameInto hs j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hr' := renameInto hr j Theta hinc
 have hg' := renameInto hg j Theta hinc
 have hw' := renameInto hw j Theta hinc
 have hv' := renameInto hv j Theta hinc
 simp only [frameRename,graph2Rename,geometryRename] at hf' hs' hp' hr' hg' hw' hv'
 exact PrefixFrameCompositionCore.composeCore R (first.relabel j) (second.relabel j) (firstCount.relabel j) (secondCount.relabel j) (firstRow.relabel j) (secondRow.relabel j) (agendaPrefix.relabel j) (produced.relabel j) (suffix.relabel j) (old.relabel j) (work.relabel j) (input.relabel j) (joined.relabel j) (output.relabel j) (middleWork.relabel j) (middleResults.relabel j) middle
   hf' hs' hp' hr' hg' hw' hv' hq
theorem withResults (R : Program 2)
 (first second firstCount secondCount firstRow secondRow agendaPrefix produced suffix old work input joined output middleWork : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (PrefixFrame R first firstCount firstRow)))
 (hs : Nonempty (Derivation body Delta (PrefixFrame R second secondCount secondRow)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append agendaPrefix first second)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced secondRow firstRow)))
 (hg : Nonempty (Derivation body Delta (geometry agendaPrefix produced suffix old work input joined output)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append middleWork second suffix)))
 : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output (add firstCount secondCount) input)) := by
 apply programCases InternalApplicationValidityStackAppend.append (Fin.cons firstRow (Fin.cons old Fin.elim0)) _
 intro beta j Theta middleResults hinc hq
 simp only [graph2Rename,addRelabel]
 simp only [consTermRename,emptyRename] at hq
 have hf' := renameInto hf j Theta hinc
 have hs' := renameInto hs j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hr' := renameInto hr j Theta hinc
 have hg' := renameInto hg j Theta hinc
 have hw' := renameInto hw j Theta hinc
 simp only [frameRename,graph2Rename,geometryRename] at hf' hs' hp' hr' hg' hw'
 exact withMiddle R (first.relabel j) (second.relabel j) (firstCount.relabel j) (secondCount.relabel j) (firstRow.relabel j) (secondRow.relabel j) (agendaPrefix.relabel j) (produced.relabel j) (suffix.relabel j) (old.relabel j) (work.relabel j) (input.relabel j) (joined.relabel j) (output.relabel j) (middleWork.relabel j) middleResults
   hf' hs' hp' hr' hg' hw' hq
theorem withWork (R : Program 2)
 (first second firstCount secondCount firstRow secondRow agendaPrefix produced suffix old work input joined output : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (PrefixFrame R first firstCount firstRow)))
 (hs : Nonempty (Derivation body Delta (PrefixFrame R second secondCount secondRow)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append agendaPrefix first second)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced secondRow firstRow)))
 (hg : Nonempty (Derivation body Delta (geometry agendaPrefix produced suffix old work input joined output)))
 : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output (add firstCount secondCount) input)) := by
 apply programCases InternalApplicationValidityStackAppend.append (Fin.cons second (Fin.cons suffix Fin.elim0)) _
 intro beta j Theta middleWork hinc hq
 simp only [graph2Rename,addRelabel]
 simp only [consTermRename,emptyRename] at hq
 have hf' := renameInto hf j Theta hinc
 have hs' := renameInto hs j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hr' := renameInto hr j Theta hinc
 have hg' := renameInto hg j Theta hinc
 simp only [frameRename,graph2Rename,geometryRename] at hf' hs' hp' hr' hg'
 exact withResults R (first.relabel j) (second.relabel j) (firstCount.relabel j) (secondCount.relabel j) (firstRow.relabel j) (secondRow.relabel j) (agendaPrefix.relabel j) (produced.relabel j) (suffix.relabel j) (old.relabel j) (work.relabel j) (input.relabel j) (joined.relabel j) (output.relabel j) middleWork
   hf' hs' hp' hr' hg' hq
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameCompositionQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameCompositionQueries
