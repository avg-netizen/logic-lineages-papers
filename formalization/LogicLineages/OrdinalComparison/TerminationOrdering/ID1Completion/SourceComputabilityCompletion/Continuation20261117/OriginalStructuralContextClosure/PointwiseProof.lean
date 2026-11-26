module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.SelectedFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.PointwiseProof
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

theorem lambda (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right domain child changed typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 lambdaConstructor left domain child)))
    (hrc : Nonempty (Derivation body Delta (graph2 lambdaConstructor right domain changed)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W false child changed)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  apply QueryProof.cons domain gamma _
  intro beta j Theta bodyGamma hj hg
  rw [checkedRename]
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  have ha' := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,
    transferRename,checkedRename,stepConsRename,stepArrowFieldsRename] at hlc' hrc' ih' ha'
  exact SelectedFieldsProof.lambda n arity M W (left.relabel j) (right.relabel j) (domain.relabel j) (child.relabel j) (changed.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) bodyGamma
    hlc' hrc' ih' hg ha'

theorem applicationFunction (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right domain child changed sibling typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 applicationConstructor left domain child sibling)))
    (hrc : Nonempty (Derivation body Delta (graph3 applicationConstructor right domain changed sibling)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W false child changed)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  apply QueryProof.cons domain typ _
  intro beta j Theta arrow hj hf
  rw [checkedRename]
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  have ha' := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,
    transferRename,checkedRename,stepConsRename,stepArrowFieldsRename] at hlc' hrc' ih' ha'
  exact AtFieldsProof.applicationFunction n arity M W (left.relabel j) (right.relabel j) (domain.relabel j) (child.relabel j) (changed.relabel j) (sibling.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) arrow
    hlc' hrc' ih' hf ha'

theorem applicationArgument (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right domain sibling child changed typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 applicationConstructor left domain sibling child)))
    (hrc : Nonempty (Derivation body Delta (graph3 applicationConstructor right domain sibling changed)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W false child changed)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  apply QueryProof.cons domain typ _
  intro beta j Theta arrow hj hf
  rw [checkedRename]
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  have ha' := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,
    transferRename,checkedRename,stepConsRename,stepArrowFieldsRename] at hlc' hrc' ih' ha'
  exact AtFieldsProof.applicationArgument n arity M W (left.relabel j) (right.relabel j) (domain.relabel j) (sibling.relabel j) (child.relabel j) (changed.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) arrow
    hlc' hrc' ih' hf ha'

theorem ordinaryBase (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right head child changed typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor left head child)))
    (hrc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor right head changed)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W true child changed)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  apply InternalAcceptanceSupportProof.programCases (signature n arity) ![head] _
  intro beta j Theta headData hj hh
  rw [checkedRename]
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  have ha' := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,
    transferRename,checkedRename,stepConsRename,stepArrowFieldsRename] at hlc' hrc' ih' ha'
  have hx : (fun i => (![head] i).relabel j) = ![head.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hh
  exact SelectedFieldsProof.ordinaryBase n arity M W (left.relabel j) (right.relabel j) (head.relabel j) (child.relabel j) (changed.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) headData
    hlc' hrc' ih' hh ha'

theorem numberedBase (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right label head recorded child changed extraTypes extras typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,head,recorded,child,extraTypes,extras])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,head,recorded,changed,extraTypes,extras])))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W true child changed)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  apply InternalAcceptanceSupportProof.programCases (signature n arity) ![head] _
  intro beta j Theta headData hj hh
  rw [checkedRename]
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  have ha' := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,
    transferRename,checkedRename,stepConsRename,stepArrowFieldsRename] at hlc' hrc' ih' ha'
  have hx : (fun i => (![head] i).relabel j) = ![head.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hh
  exact SelectedFieldsProof.numberedBase n arity M W (left.relabel j) (right.relabel j) (label.relabel j) (head.relabel j) (recorded.relabel j) (child.relabel j) (changed.relabel j) (extraTypes.relabel j) (extras.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) headData
    hlc' hrc' ih' hh ha'

theorem numberedExtras (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right label head recorded base extraTypes child changed typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,head,recorded,base,extraTypes,child])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,head,recorded,base,extraTypes,changed])))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W true child changed)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  apply InternalAcceptanceSupportProof.programCases (signature n arity) ![head] _
  intro beta j Theta headData hj hh
  rw [checkedRename]
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have ih' := renameInto ih j Theta hj
  have ha' := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,programRename,
    InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename,
    OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename,
    transferRename,checkedRename,stepConsRename,stepArrowFieldsRename] at hlc' hrc' ih' ha'
  have hx : (fun i => (![head] i).relabel j) = ![head.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hh
  exact SelectedFieldsProof.numberedExtras n arity M W (left.relabel j) (right.relabel j) (label.relabel j) (head.relabel j) (recorded.relabel j) (base.relabel j) (extraTypes.relabel j) (child.relabel j) (changed.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) headData
    hlc' hrc' ih' hh ha'

theorem argumentsHead (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right domain child changed tail typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 consConstructor left domain child tail)))
    (hrc : Nonempty (Derivation body Delta (graph3 consConstructor right domain changed tail)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W false child changed)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W true typ left gamma context))) :
    Nonempty (Derivation body Delta (Checked n arity M W true typ right gamma context)) := by
  exact SelectedFieldsProof.argumentsHead n arity M W left right domain child changed tail typ gamma context hlc hrc ih ha

theorem argumentsTail (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right domain head child changed typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 consConstructor left domain head child)))
    (hrc : Nonempty (Derivation body Delta (graph3 consConstructor right domain head changed)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W true child changed)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W true typ left gamma context))) :
    Nonempty (Derivation body Delta (Checked n arity M W true typ right gamma context)) := by
  exact SelectedFieldsProof.argumentsTail n arity M W left right domain head child changed typ gamma context hlc hrc ih ha
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.PointwiseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.PointwiseProof
