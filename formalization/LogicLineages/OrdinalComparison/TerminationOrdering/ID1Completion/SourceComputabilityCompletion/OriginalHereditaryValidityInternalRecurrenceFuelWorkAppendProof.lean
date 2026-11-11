module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionSplitProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelAppendInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationSaturationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof InternalAdditionLawsProof
open InternalGraphCompositionFunctionalityProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
open OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceIterationWorkProof
open OriginalHereditaryValidityInternalRecurrenceIterationSaturationSupportProof
open OriginalHereditaryValidityInternalRecurrenceIterationSaturationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The split runs use one common count; internal saturation removes its
surplus over each component's independently computed original work fuel. -/
theorem forwardAtWeights (s t m : Program 2) (front suffix joined first second : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hf : Nonempty (Derivation body Delta (WorkFuelGraph first front)))
    (hs : Nonempty (Derivation body Delta (WorkFuelGraph second suffix)))
    (hj : Nonempty (Derivation body Delta (WorkAccepted s t m joined))) :
    Nonempty (Derivation body Delta (WorkAccepted s t m front ⊓ WorkAccepted s t m suffix)) := by
  have hw := OriginalHereditaryValidityInternalRecurrenceFuelAppendInductionProof.appendValue
    front suffix joined first second ha hf hs
  have hr := acceptedAtOwnFuel s t m (add first second) joined hw hj
  have hparts := OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionSplitProof.successfulSplit
    s t m (add first second) front suffix joined ha hr
  exact andIntro
    (saturatedForward s t m first (add first second) front hf
      (InternalUnpairArithmeticProof.leftWeakAdd first second) (andLeft hparts))
    (saturatedForward s t m second (add first second) suffix hs
      (InternalUnpairReverseBoundsArithmeticProof.rightWeakAdd first second) (andRight hparts))

theorem backwardAtWeights (s t m : Program 2) (front suffix joined first second : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hf : Nonempty (Derivation body Delta (WorkFuelGraph first front)))
    (hs : Nonempty (Derivation body Delta (WorkFuelGraph second suffix)))
    (hfront : Nonempty (Derivation body Delta (WorkAccepted s t m front)))
    (hsuffix : Nonempty (Derivation body Delta (WorkAccepted s t m suffix))) :
    Nonempty (Derivation body Delta (WorkAccepted s t m joined)) := by
  have hw := OriginalHereditaryValidityInternalRecurrenceFuelAppendInductionProof.appendValue
    front suffix joined first second ha hf hs
  have hr := OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionProof.successfulAppend
    s t m first second front suffix joined ha
    (acceptedAtOwnFuel s t m first front hf hfront)
    (acceptedAtOwnFuel s t m second suffix hs hsuffix)
  exact acceptedIntro s t m joined (add first second) hw hr

def fuelQueries : Fin 2 → Program 2 :=
  fun i => .composition workFuel (fun _ : Fin 1 => .projection i)

theorem appendForward (s t m : Program 2) (front suffix joined : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hj : Nonempty (Derivation body Delta (WorkAccepted s t m joined))) :
    Nonempty (Derivation body Delta (WorkAccepted s t m front ⊓ WorkAccepted s t m suffix)) := by
  apply queryCases fuelQueries (Fin.cons front (Fin.cons suffix Fin.elim0)) _
  intro beta j ys Theta hinc hq
  change Nonempty (Derivation body Theta
    ((WorkAccepted s t m front).relabel j ⊓ (WorkAccepted s t m suffix).relabel j))
  rw [workAcceptedRename,workAcceptedRename]
  simp only [consTermRename,emptyRename] at hq
  have ha' := renameInto ha j Theta hinc
  rw [graph2Rename] at ha'
  have hj' := renameInto hj j Theta hinc
  rw [workAcceptedRename] at hj'
  let xs : Fin 2 → OTerm beta := Fin.cons (front.relabel j) (Fin.cons (suffix.relabel j) Fin.elim0)
  have hf := unaryRecover workFuel (.projection 0) (ys 0) (front.relabel j) xs (hq 0) (projectionValue 0 xs)
  have hs := unaryRecover workFuel (.projection 1) (ys 1) (suffix.relabel j) xs (hq 1) (projectionValue 1 xs)
  exact forwardAtWeights s t m (front.relabel j) (suffix.relabel j) (joined.relabel j) (ys 0) (ys 1) ha' hf hs hj'

theorem appendBackward (s t m : Program 2) (front suffix joined : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hfront : Nonempty (Derivation body Delta (WorkAccepted s t m front)))
    (hsuffix : Nonempty (Derivation body Delta (WorkAccepted s t m suffix))) :
    Nonempty (Derivation body Delta (WorkAccepted s t m joined)) := by
  apply queryCases fuelQueries (Fin.cons front (Fin.cons suffix Fin.elim0)) _
  intro beta j ys Theta hinc hq
  rw [workAcceptedRename]
  simp only [consTermRename,emptyRename] at hq
  have ha' := renameInto ha j Theta hinc
  rw [graph2Rename] at ha'
  have hf' := renameInto hfront j Theta hinc
  have hs' := renameInto hsuffix j Theta hinc
  rw [workAcceptedRename] at hf' hs'
  let xs : Fin 2 → OTerm beta := Fin.cons (front.relabel j) (Fin.cons (suffix.relabel j) Fin.elim0)
  have hf := unaryRecover workFuel (.projection 0) (ys 0) (front.relabel j) xs (hq 0) (projectionValue 0 xs)
  have hs := unaryRecover workFuel (.projection 1) (ys 1) (suffix.relabel j) xs (hq 1) (projectionValue 1 xs)
  exact backwardAtWeights s t m (front.relabel j) (suffix.relabel j) (joined.relabel j) (ys 0) (ys 1)
    ha' hf hs hf' hs'

theorem actualOriginalHereditaryInternalWorkAppend :
    OriginalHereditaryValidityInternalRecurrenceTargets.ActualOriginalHereditaryInternalWorkAppend := by
  intro body s t m alpha front suffix joined
  let H := graph2 InternalApplicationValidityStackAppend.append joined front suffix
  let P := WorkAccepted s t m joined
  let Q := WorkAccepted s t m front ⊓ WorkAccepted s t m suffix
  have ha : Nonempty (Derivation body [H] H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := appendForward s t m front suffix joined (withHyp ha P)
    (show Nonempty (Derivation body [P,H] P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have hq : Nonempty (Derivation body [Q,H] Q) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := appendBackward s t m front suffix joined (withHyp ha Q) (andLeft hq) (andRight hq)
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendProof
