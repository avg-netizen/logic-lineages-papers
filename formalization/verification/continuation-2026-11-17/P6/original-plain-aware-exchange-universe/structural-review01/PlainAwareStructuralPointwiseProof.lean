module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralSelectedFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralPointwiseProof
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
    (left right domain child changed typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 lambdaConstructor left domain child)))
    (hrc : Nonempty (Derivation body Delta (graph2 lambdaConstructor right domain changed)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W false child changed context)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (Plain n arity false typ right gamma))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  apply OriginalStructuralContextClosure.QueryProof.cons domain gamma _
  intro beta j Theta bodyGamma hj hg
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
  exact PlainAwareStructuralSelectedFieldsProof.lambda n arity M W (left.relabel j) (right.relabel j) (domain.relabel j) (child.relabel j) (changed.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) bodyGamma
    hlc' hrc' ih' hg ha' hp'

theorem applicationFunction (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right domain child changed sibling typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 applicationConstructor left domain child sibling)))
    (hrc : Nonempty (Derivation body Delta (graph3 applicationConstructor right domain changed sibling)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W false child changed context)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (Plain n arity false typ right gamma))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  apply OriginalStructuralContextClosure.QueryProof.cons domain typ _
  intro beta j Theta arrow hj hf
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
  exact PlainAwareStructuralAtFieldsProof.applicationFunction n arity M W (left.relabel j) (right.relabel j) (domain.relabel j) (child.relabel j) (changed.relabel j) (sibling.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) arrow
    hlc' hrc' ih' hf ha' hp'

theorem applicationArgument (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right domain sibling child changed typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 applicationConstructor left domain sibling child)))
    (hrc : Nonempty (Derivation body Delta (graph3 applicationConstructor right domain sibling changed)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W false child changed context)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (Plain n arity false typ right gamma))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  apply OriginalStructuralContextClosure.QueryProof.cons domain typ _
  intro beta j Theta arrow hj hf
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
  exact PlainAwareStructuralAtFieldsProof.applicationArgument n arity M W (left.relabel j) (right.relabel j) (domain.relabel j) (sibling.relabel j) (child.relabel j) (changed.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) arrow
    hlc' hrc' ih' hf ha' hp'

theorem ordinaryBase (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right head child changed typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor left head child)))
    (hrc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor right head changed)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W true child changed context)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (Plain n arity false typ right gamma))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  apply InternalAcceptanceSupportProof.programCases (signature n arity) ![head] _
  intro beta j Theta headData hj hh
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
  have hx : (fun i => (![head] i).relabel j) = ![head.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hh
  exact PlainAwareStructuralSelectedFieldsProof.ordinaryBase n arity M W (left.relabel j) (right.relabel j) (head.relabel j) (child.relabel j) (changed.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) headData
    hlc' hrc' ih' hh ha' hp'

theorem numberedBase (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right label head recorded child changed extraTypes extras typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,head,recorded,child,extraTypes,extras])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,head,recorded,changed,extraTypes,extras])))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W true child changed context)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (Plain n arity false typ right gamma))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  apply InternalAcceptanceSupportProof.programCases (signature n arity) ![head] _
  intro beta j Theta headData hj hh
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
  have hx : (fun i => (![head] i).relabel j) = ![head.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hh
  exact PlainAwareStructuralSelectedFieldsProof.numberedBase n arity M W (left.relabel j) (right.relabel j) (label.relabel j) (head.relabel j) (recorded.relabel j) (child.relabel j) (changed.relabel j) (extraTypes.relabel j) (extras.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) headData
    hlc' hrc' ih' hh ha' hp'

theorem numberedExtras (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right label head recorded base extraTypes child changed typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,head,recorded,base,extraTypes,child])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,head,recorded,base,extraTypes,changed])))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W true child changed context)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (Plain n arity false typ right gamma))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  apply InternalAcceptanceSupportProof.programCases (signature n arity) ![head] _
  intro beta j Theta headData hj hh
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
  have hx : (fun i => (![head] i).relabel j) = ![head.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hh
  exact PlainAwareStructuralSelectedFieldsProof.numberedExtras n arity M W (left.relabel j) (right.relabel j) (label.relabel j) (head.relabel j) (recorded.relabel j) (base.relabel j) (extraTypes.relabel j) (child.relabel j) (changed.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) headData
    hlc' hrc' ih' hh ha' hp'

theorem argumentsHead (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right domain child changed tail typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 consConstructor left domain child tail)))
    (hrc : Nonempty (Derivation body Delta (graph3 consConstructor right domain changed tail)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W false child changed context)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W true typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (Plain n arity true typ right gamma))) :
    Nonempty (Derivation body Delta (Checked n arity M W true typ right gamma context)) := by
  exact PlainAwareStructuralSelectedFieldsProof.argumentsHead n arity M W left right domain child changed tail typ gamma context hlc hrc ih ha

theorem argumentsTail (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right domain head child changed typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 consConstructor left domain head child)))
    (hrc : Nonempty (Derivation body Delta (graph3 consConstructor right domain head changed)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W true child changed context)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W true typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (Plain n arity true typ right gamma))) :
    Nonempty (Derivation body Delta (Checked n arity M W true typ right gamma context)) := by
  exact PlainAwareStructuralSelectedFieldsProof.argumentsTail n arity M W left right domain head child changed typ gamma context hlc hrc ih ha
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralPointwiseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralPointwiseProof
