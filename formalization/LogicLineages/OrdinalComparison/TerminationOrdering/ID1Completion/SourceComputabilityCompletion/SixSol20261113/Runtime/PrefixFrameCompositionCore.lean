module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameIdentityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.AppendReassociationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameCompositionCore
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
theorem composeCore (R : Program 2)
 (first second firstCount secondCount firstRow secondRow agendaPrefix produced
 suffix old work input joined output middleWork middleResults middle : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (PrefixFrame R first firstCount firstRow)))
 (hs : Nonempty (Derivation body Delta (PrefixFrame R second secondCount secondRow)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append agendaPrefix first second)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced secondRow firstRow)))
 (hg : Nonempty (Derivation body Delta (geometry agendaPrefix produced suffix old work input joined output)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append middleWork second suffix)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append middleResults firstRow old)))
 (hm : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing middle middleWork middleResults))) :
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output (add firstCount secondCount) input)) := by
 have ha := SixSol20261112.Runtime.AppendReassociationProof.appendReassociation body alpha Delta
   first second suffix agendaPrefix middleWork work hp hw (andLeft hg)
 have hb := SixSol20261112.Runtime.AppendReassociationProof.appendReassociation body alpha Delta
   secondRow firstRow old produced middleResults joined hr hv (andLeft (andRight (andRight hg)))
 have hfirst := frameApply R first firstCount firstRow middleWork old work input middleResults middle
   hf (andIntro ha (andIntro (andLeft (andRight hg)) (andIntro hv hm)))
 have hsecond := frameApply R second secondCount secondRow suffix middleResults middleWork middle joined output
   hs (andIntro hw (andIntro hm (andIntro hb (andRight (andRight (andRight hg))))))
 exact InternalNumericIterationFusionProof.fusionValue (OriginalHereditaryCombinedStep.step R)
   firstCount secondCount input middle output hfirst hsecond
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameCompositionCore
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameCompositionCore
