module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralPointwiseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralClosureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PlainAwareStructuralDefinitions PlainAwareStructuralSyntaxProof PlainAwareStructuralBindingProof
open Continuation20261116.OriginalConcreteHeadSignature
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem lambda : PlainAwareStructuralTargets.InternalLambda := by
  intro n arity M W body alpha Delta left right domain child changed context hlc hrc _hlg _hrg ih
  apply transferIntro n arity M W false left right context
  intro beta j Theta typ gamma hj ha hp
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  simp only [graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,transferRename] at hlc' hrc' ih'
  exact PlainAwareStructuralPointwiseProof.lambda n arity M W (left.relabel j) (right.relabel j) (domain.relabel j) (child.relabel j) (changed.relabel j) typ gamma (context.relabel j) hlc' hrc' ih' ha hp

theorem applicationFunction : PlainAwareStructuralTargets.InternalApplicationFunction := by
  intro n arity M W body alpha Delta left right domain child changed sibling context hlc hrc _hlg _hrg ih
  apply transferIntro n arity M W false left right context
  intro beta j Theta typ gamma hj ha hp
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  simp only [graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,transferRename] at hlc' hrc' ih'
  exact PlainAwareStructuralPointwiseProof.applicationFunction n arity M W (left.relabel j) (right.relabel j) (domain.relabel j) (child.relabel j) (changed.relabel j) (sibling.relabel j) typ gamma (context.relabel j) hlc' hrc' ih' ha hp

theorem applicationArgument : PlainAwareStructuralTargets.InternalApplicationArgument := by
  intro n arity M W body alpha Delta left right domain sibling child changed context hlc hrc _hlg _hrg ih
  apply transferIntro n arity M W false left right context
  intro beta j Theta typ gamma hj ha hp
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  simp only [graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,transferRename] at hlc' hrc' ih'
  exact PlainAwareStructuralPointwiseProof.applicationArgument n arity M W (left.relabel j) (right.relabel j) (domain.relabel j) (sibling.relabel j) (child.relabel j) (changed.relabel j) typ gamma (context.relabel j) hlc' hrc' ih' ha hp

theorem ordinaryBase : PlainAwareStructuralTargets.InternalOrdinaryBase := by
  intro n arity M W body alpha Delta left right head child changed context hlc hrc _hlg _hrg ih
  apply transferIntro n arity M W false left right context
  intro beta j Theta typ gamma hj ha hp
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  simp only [graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,transferRename] at hlc' hrc' ih'
  exact PlainAwareStructuralPointwiseProof.ordinaryBase n arity M W (left.relabel j) (right.relabel j) (head.relabel j) (child.relabel j) (changed.relabel j) typ gamma (context.relabel j) hlc' hrc' ih' ha hp

theorem numberedBase : PlainAwareStructuralTargets.InternalNumberedBase := by
  intro n arity M W body alpha Delta left right label head recorded child changed extraTypes extras context hlc hrc _hlg _hrg ih
  apply transferIntro n arity M W false left right context
  intro beta j Theta typ gamma hj ha hp
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  simp only [graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,transferRename] at hlc' hrc' ih'
  exact PlainAwareStructuralPointwiseProof.numberedBase n arity M W (left.relabel j) (right.relabel j) (label.relabel j) (head.relabel j) (recorded.relabel j) (child.relabel j) (changed.relabel j) (extraTypes.relabel j) (extras.relabel j) typ gamma (context.relabel j) hlc' hrc' ih' ha hp

theorem numberedExtras : PlainAwareStructuralTargets.InternalNumberedExtras := by
  intro n arity M W body alpha Delta left right label head recorded base extraTypes child changed context hlc hrc _hlg _hrg ih
  apply transferIntro n arity M W false left right context
  intro beta j Theta typ gamma hj ha hp
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  simp only [graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,transferRename] at hlc' hrc' ih'
  exact PlainAwareStructuralPointwiseProof.numberedExtras n arity M W (left.relabel j) (right.relabel j) (label.relabel j) (head.relabel j) (recorded.relabel j) (base.relabel j) (extraTypes.relabel j) (child.relabel j) (changed.relabel j) typ gamma (context.relabel j) hlc' hrc' ih' ha hp

theorem argumentsHead : PlainAwareStructuralTargets.InternalArgumentsHead := by
  intro n arity M W body alpha Delta left right domain child changed tail context hlc hrc _hlg _hrg ih
  apply transferIntro n arity M W true left right context
  intro beta j Theta typ gamma hj ha hp
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  simp only [graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,transferRename] at hlc' hrc' ih'
  exact PlainAwareStructuralPointwiseProof.argumentsHead n arity M W (left.relabel j) (right.relabel j) (domain.relabel j) (child.relabel j) (changed.relabel j) (tail.relabel j) typ gamma (context.relabel j) hlc' hrc' ih' ha hp

theorem argumentsTail : PlainAwareStructuralTargets.InternalArgumentsTail := by
  intro n arity M W body alpha Delta left right domain head child changed context hlc hrc _hlg _hrg ih
  apply transferIntro n arity M W true left right context
  intro beta j Theta typ gamma hj ha hp
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  simp only [graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,transferRename] at hlc' hrc' ih'
  exact PlainAwareStructuralPointwiseProof.argumentsTail n arity M W (left.relabel j) (right.relabel j) (domain.relabel j) (head.relabel j) (child.relabel j) (changed.relabel j) typ gamma (context.relabel j) hlc' hrc' ih' ha hp

theorem structuralContextClosure : PlainAwareStructuralTargets.InternalStructuralContextClosure :=
  ⟨lambda,applicationFunction,applicationArgument,ordinaryBase,numberedBase,numberedExtras,argumentsHead,argumentsTail⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralClosureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralClosureProof
