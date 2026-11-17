module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.QueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralAtFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralSelectedFieldsProof
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

theorem lambda (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right domain child changed typ gamma context bodyGamma : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 lambdaConstructor left domain child)))
    (hrc : Nonempty (Derivation body Delta (graph2 lambdaConstructor right domain changed)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W false child changed context)))
    (hg : Nonempty (Derivation body Delta (StepCons bodyGamma domain gamma)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (Plain n arity false typ right gamma))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  apply OriginalStructuralContextClosure.QueryProof.fields typ _
  intro beta j Theta requested codomain hj hf
  rw [checkedRename]
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  have hg' := renameInto hg j Theta hj
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,
    transferRename,checkedRename,plainRename,stepConsRename,stepArrowFieldsRename] at hlc' hrc' ih' hg' ha' hp'
  exact PlainAwareStructuralAtFieldsProof.lambda n arity M W (left.relabel j) (right.relabel j) (domain.relabel j) (child.relabel j) (changed.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) requested codomain (bodyGamma.relabel j)
    hlc' hrc' ih' hf hg' ha' hp'

theorem ordinaryBase (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right head child changed typ gamma context headData : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor left head child)))
    (hrc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor right head changed)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W true child changed context)))
    (hh : Nonempty (Derivation body Delta (graph1 (signature n arity) headData head)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (Plain n arity false typ right gamma))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  apply OriginalStructuralContextClosure.QueryProof.fields headData _
  intro beta j Theta result types hj hf
  rw [checkedRename]
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  have hh' := renameInto hh j Theta hj
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,
    transferRename,checkedRename,plainRename,stepConsRename,stepArrowFieldsRename] at hlc' hrc' ih' hh' ha' hp'
  exact PlainAwareStructuralAtFieldsProof.ordinaryBase n arity M W (left.relabel j) (right.relabel j) (head.relabel j) (child.relabel j) (changed.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) (headData.relabel j) result types
    hlc' hrc' ih' hh' hf ha' hp'

theorem numberedBase (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right label head recorded child changed extraTypes extras typ gamma context headData : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,head,recorded,child,extraTypes,extras])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,head,recorded,changed,extraTypes,extras])))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W true child changed context)))
    (hh : Nonempty (Derivation body Delta (graph1 (signature n arity) headData head)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (Plain n arity false typ right gamma))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  apply OriginalStructuralContextClosure.QueryProof.fields headData _
  intro beta j Theta result types hj hf
  rw [checkedRename]
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  have hh' := renameInto hh j Theta hj
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,
    transferRename,checkedRename,plainRename,stepConsRename,stepArrowFieldsRename] at hlc' hrc' ih' hh' ha' hp'
  exact PlainAwareStructuralAtFieldsProof.numberedBase n arity M W (left.relabel j) (right.relabel j) (label.relabel j) (head.relabel j) (recorded.relabel j) (child.relabel j) (changed.relabel j) (extraTypes.relabel j) (extras.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) (headData.relabel j) result types
    hlc' hrc' ih' hh' hf ha' hp'

theorem numberedExtras (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right label head recorded base extraTypes child changed typ gamma context headData : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,head,recorded,base,extraTypes,child])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,head,recorded,base,extraTypes,changed])))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W true child changed context)))
    (hh : Nonempty (Derivation body Delta (graph1 (signature n arity) headData head)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (Plain n arity false typ right gamma))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  apply OriginalStructuralContextClosure.QueryProof.fields headData _
  intro beta j Theta result types hj hf
  rw [checkedRename]
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  have hh' := renameInto hh j Theta hj
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,
    transferRename,checkedRename,plainRename,stepConsRename,stepArrowFieldsRename] at hlc' hrc' ih' hh' ha' hp'
  exact PlainAwareStructuralAtFieldsProof.numberedExtras n arity M W (left.relabel j) (right.relabel j) (label.relabel j) (head.relabel j) (recorded.relabel j) (base.relabel j) (extraTypes.relabel j) (child.relabel j) (changed.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) (headData.relabel j) result types
    hlc' hrc' ih' hh' hf ha' hp'

theorem argumentsHead (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right domain child changed tail typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 consConstructor left domain child tail)))
    (hrc : Nonempty (Derivation body Delta (graph3 consConstructor right domain changed tail)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W false child changed context)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W true typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (Plain n arity true typ right gamma))) :
    Nonempty (Derivation body Delta (Checked n arity M W true typ right gamma context)) := by
  apply OriginalStructuralContextClosure.QueryProof.fields typ _
  intro beta j Theta requested tailTypes hj hf
  rw [checkedRename]
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,
    transferRename,checkedRename,plainRename,stepConsRename,stepArrowFieldsRename] at hlc' hrc' ih' ha' hp'
  exact PlainAwareStructuralAtFieldsProof.argumentsHead n arity M W (left.relabel j) (right.relabel j) (domain.relabel j) (child.relabel j) (changed.relabel j) (tail.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) requested tailTypes
    hlc' hrc' ih' hf ha' hp'

theorem argumentsTail (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right domain head child changed typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 consConstructor left domain head child)))
    (hrc : Nonempty (Derivation body Delta (graph3 consConstructor right domain head changed)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W true child changed context)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W true typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (Plain n arity true typ right gamma))) :
    Nonempty (Derivation body Delta (Checked n arity M W true typ right gamma context)) := by
  apply OriginalStructuralContextClosure.QueryProof.fields typ _
  intro beta j Theta requested tailTypes hj hf
  rw [checkedRename]
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,
    transferRename,checkedRename,plainRename,stepConsRename,stepArrowFieldsRename] at hlc' hrc' ih' ha' hp'
  exact PlainAwareStructuralAtFieldsProof.argumentsTail n arity M W (left.relabel j) (right.relabel j) (domain.relabel j) (head.relabel j) (child.relabel j) (changed.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) requested tailTypes
    hlc' hrc' ih' hf ha' hp'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralSelectedFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralSelectedFieldsProof
