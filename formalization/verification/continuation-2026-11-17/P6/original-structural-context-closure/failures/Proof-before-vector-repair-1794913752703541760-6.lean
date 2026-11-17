module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.PointwiseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Definitions SyntaxProof BindingProof
open Continuation20261116.OriginalConcreteHeadSignature
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem lambda : Targets.InternalLambda := by
  intro n arity M W body alpha Delta left right domain child changed hlc hrc _hlg _hrg ih
  apply transferIntro n arity M W false left right
  intro beta j Theta typ gamma context hj ha
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  simp only [graph2Rename,graph3Rename,programRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,transferRename] at hlc' hrc' ih'
  exact PointwiseProof.lambda n arity M W (left.relabel j) (right.relabel j) (domain.relabel j) (child.relabel j) (changed.relabel j) typ gamma context hlc' hrc' ih' ha

theorem applicationFunction : Targets.InternalApplicationFunction := by
  intro n arity M W body alpha Delta left right domain child changed sibling hlc hrc _hlg _hrg ih
  apply transferIntro n arity M W false left right
  intro beta j Theta typ gamma context hj ha
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  simp only [graph2Rename,graph3Rename,programRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,transferRename] at hlc' hrc' ih'
  exact PointwiseProof.applicationFunction n arity M W (left.relabel j) (right.relabel j) (domain.relabel j) (child.relabel j) (changed.relabel j) (sibling.relabel j) typ gamma context hlc' hrc' ih' ha

theorem applicationArgument : Targets.InternalApplicationArgument := by
  intro n arity M W body alpha Delta left right domain sibling child changed hlc hrc _hlg _hrg ih
  apply transferIntro n arity M W false left right
  intro beta j Theta typ gamma context hj ha
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  simp only [graph2Rename,graph3Rename,programRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,transferRename] at hlc' hrc' ih'
  exact PointwiseProof.applicationArgument n arity M W (left.relabel j) (right.relabel j) (domain.relabel j) (sibling.relabel j) (child.relabel j) (changed.relabel j) typ gamma context hlc' hrc' ih' ha

theorem ordinaryBase : Targets.InternalOrdinaryBase := by
  intro n arity M W body alpha Delta left right head child changed hlc hrc _hlg _hrg ih
  apply transferIntro n arity M W false left right
  intro beta j Theta typ gamma context hj ha
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  simp only [graph2Rename,graph3Rename,programRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,transferRename] at hlc' hrc' ih'
  exact PointwiseProof.ordinaryBase n arity M W (left.relabel j) (right.relabel j) (head.relabel j) (child.relabel j) (changed.relabel j) typ gamma context hlc' hrc' ih' ha

theorem numberedBase : Targets.InternalNumberedBase := by
  intro n arity M W body alpha Delta left right label head recorded child changed extraTypes extras hlc hrc _hlg _hrg ih
  apply transferIntro n arity M W false left right
  intro beta j Theta typ gamma context hj ha
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  simp only [graph2Rename,graph3Rename,programRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,transferRename] at hlc' hrc' ih'
  exact PointwiseProof.numberedBase n arity M W (left.relabel j) (right.relabel j) (label.relabel j) (head.relabel j) (recorded.relabel j) (child.relabel j) (changed.relabel j) (extraTypes.relabel j) (extras.relabel j) typ gamma context hlc' hrc' ih' ha

theorem numberedExtras : Targets.InternalNumberedExtras := by
  intro n arity M W body alpha Delta left right label head recorded base extraTypes child changed hlc hrc _hlg _hrg ih
  apply transferIntro n arity M W false left right
  intro beta j Theta typ gamma context hj ha
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  simp only [graph2Rename,graph3Rename,programRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,transferRename] at hlc' hrc' ih'
  exact PointwiseProof.numberedExtras n arity M W (left.relabel j) (right.relabel j) (label.relabel j) (head.relabel j) (recorded.relabel j) (base.relabel j) (extraTypes.relabel j) (child.relabel j) (changed.relabel j) typ gamma context hlc' hrc' ih' ha

theorem argumentsHead : Targets.InternalArgumentsHead := by
  intro n arity M W body alpha Delta left right domain child changed tail hlc hrc _hlg _hrg ih
  apply transferIntro n arity M W true left right
  intro beta j Theta typ gamma context hj ha
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  simp only [graph2Rename,graph3Rename,programRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,transferRename] at hlc' hrc' ih'
  exact PointwiseProof.argumentsHead n arity M W (left.relabel j) (right.relabel j) (domain.relabel j) (child.relabel j) (changed.relabel j) (tail.relabel j) typ gamma context hlc' hrc' ih' ha

theorem argumentsTail : Targets.InternalArgumentsTail := by
  intro n arity M W body alpha Delta left right domain head child changed hlc hrc _hlg _hrg ih
  apply transferIntro n arity M W true left right
  intro beta j Theta typ gamma context hj ha
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  simp only [graph2Rename,graph3Rename,programRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,transferRename] at hlc' hrc' ih'
  exact PointwiseProof.argumentsTail n arity M W (left.relabel j) (right.relabel j) (domain.relabel j) (head.relabel j) (child.relabel j) (changed.relabel j) typ gamma context hlc' hrc' ih' ha

theorem structuralContextClosure : Targets.InternalStructuralContextClosure :=
  ⟨lambda,applicationFunction,applicationArgument,ordinaryBase,numberedBase,numberedExtras,argumentsHead,argumentsTail⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.Proof
