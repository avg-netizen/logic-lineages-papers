module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSpecSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSpecProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof
open InternalOriginalPairingOrderArithmeticProof (withHyp formulaCases)
open SourceComputabilityFormulaSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalVariableLeafProof
open OriginalRawSyntaxTransportInternalVariableEraseLeafProof
open OriginalRawSyntaxTransportInternalVariableSpecSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem eraseAbovePrevious (raw out d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (hgt : Nonempty (Derivation body Delta (InternalLessThan.strictLess k i)))
    (ho : Nonempty (Derivation body Delta (graph3 (leaf .erase) out d k raw))) :
    Nonempty (Derivation body Delta (PreviousResult out i)) := by
  apply programCases InternalEqualityTest.predecessor (Fin.cons i Fin.elim0) _
  intro beta j Theta previous hj hp
  rw [previousRename]
  simp only [consTermRename,emptyRename] at hp
  have hr' := renameInto hr j Theta hj
  have ho' := renameInto ho j Theta hj
  have hg' := renameInto hgt j Theta hj
  rw [graph1Rename] at hr'
  rw [graph3Rename] at ho'
  change Nonempty (Derivation body Theta ((InternalLessThan.strictLess k i).relabel j)) at hg'
  simp only [InternalLessThan.strictLess,orderRename] at hg'
  exact previousIntro (out.relabel j) (i.relabel j) previous hp
    (eraseLeafAboveForwardAt (raw.relabel j) (out.relabel j) (d.relabel j) (k.relabel j)
      (i.relabel j) previous hr' hg' hp ho')

theorem eraseAboveFromPrevious (raw out d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (hgt : Nonempty (Derivation body Delta (InternalLessThan.strictLess k i)))
    (ho : Nonempty (Derivation body Delta (PreviousResult out i))) :
    Nonempty (Derivation body Delta (graph3 (leaf .erase) out d k raw)) := by
  apply previousCases out i _ ho
  intro beta j Theta previous hj hp hv
  rw [graph3Rename]
  have hr' := renameInto hr j Theta hj
  have hg' := renameInto hgt j Theta hj
  rw [graph1Rename] at hr'
  simp only [InternalLessThan.strictLess,orderRename] at hg'
  exact eraseLeafAboveBackwardAt (raw.relabel j) (out.relabel j) (d.relabel j) (k.relabel j)
    (i.relabel j) previous hr' hg' hp hv

/-- Literal variable branches of the frozen leaf, using internal comparison
and existential predecessor witnesses on completely symbolic arithmetic inputs. -/
theorem variableLeafSpecForward (mode : Mode) (raw out d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (ho : Nonempty (Derivation body Delta (graph3 (leaf mode) out d k raw))) :
    Nonempty (Derivation body Delta (VariableSpec mode out d k i)) := by
  cases mode with
  | rank => exact rankLeafForward raw out d k i hr ho
  | shift =>
    apply formulaCases (InternalLessThan.strictLess i k)
    · have hl : Nonempty (Derivation body (InternalLessThan.strictLess i k :: Delta)
          (InternalLessThan.strictLess i k)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hv := shiftLeafForwardAt raw out d k i i (withHyp hr _)
        (shiftChoiceBelow raw d k i (withHyp hr _) hl) (withHyp ho _)
      obtain ⟨hl⟩ := hl
      obtain ⟨hv⟩ := hv
      exact ⟨orLeft (Derivation.conjunctionIntroduction hl hv)⟩
    · have hl : Nonempty (Derivation body ((InternalLessThan.strictLess i k).not :: Delta)
          (InternalLessThan.strictLess i k).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hv := shiftLeafForwardAt raw out d k i (suc i) (withHyp hr _)
        (shiftChoiceNotBelow raw d k i (withHyp hr _) hl) (withHyp ho _)
      obtain ⟨hl⟩ := hl
      obtain ⟨hv⟩ := hv
      exact ⟨orRight (Derivation.conjunctionIntroduction hl hv)⟩
  | erase =>
    apply indexCases i k
    · have hl : Nonempty (Derivation body (InternalLessThan.strictLess i k :: Delta)
          (InternalLessThan.strictLess i k)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      obtain ⟨hv⟩ := eraseLeafBelowForward raw out d k i (withHyp hr _) hl (withHyp ho _)
      obtain ⟨hl⟩ := hl
      exact ⟨orLeft (Derivation.conjunctionIntroduction hl hv)⟩
    · have he : Nonempty (Derivation body (equal i k :: Delta) (equal i k)) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      obtain ⟨hv⟩ := eraseLeafEqualForward raw out d k i (withHyp hr _) he (withHyp ho _)
      obtain ⟨he⟩ := he
      exact ⟨orRight (orLeft (Derivation.conjunctionIntroduction he hv))⟩
    · have hg : Nonempty (Derivation body (InternalLessThan.strictLess k i :: Delta)
          (InternalLessThan.strictLess k i)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      obtain ⟨hv⟩ := eraseAbovePrevious raw out d k i (withHyp hr _) hg (withHyp ho _)
      obtain ⟨hg⟩ := hg
      exact ⟨orRight (orRight (Derivation.conjunctionIntroduction hg hv))⟩

theorem variableLeafSpecBackward (mode : Mode) (raw out d k i : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 variableConstructor raw i)))
    (ho : Nonempty (Derivation body Delta (VariableSpec mode out d k i))) :
    Nonempty (Derivation body Delta (graph3 (leaf mode) out d k raw)) := by
  cases mode with
  | rank => exact rankLeafBackward raw out d k i hr ho
  | shift =>
    apply orCases ho
    · let A := InternalLessThan.strictLess i k ⊓ graph1 variableConstructor out i
      have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact shiftLeafBackwardAt raw out d k i i (withHyp hr A)
        (shiftChoiceBelow raw d k i (withHyp hr A) (andLeft h)) (andRight h)
    · let A := (InternalLessThan.strictLess i k).not ⊓ graph1 variableConstructor out (suc i)
      have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact shiftLeafBackwardAt raw out d k i (suc i) (withHyp hr A)
        (shiftChoiceNotBelow raw d k i (withHyp hr A) (andLeft h)) (andRight h)
  | erase =>
    apply orCases ho
    · let A := InternalLessThan.strictLess i k ⊓ graph1 variableConstructor out i
      have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact eraseLeafBelowBackward raw out d k i (withHyp hr A) (andLeft h) (andRight h)
    · let A := (equal i k ⊓ graph1 bottomConstructor out d) ⊔
        (InternalLessThan.strictLess k i ⊓ PreviousResult out i)
      have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      apply orCases h
      · let B := equal i k ⊓ graph1 bottomConstructor out d
        have hb : Nonempty (Derivation body (B :: A :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
        exact eraseLeafEqualBackward raw out d k i (withHyp (withHyp hr A) B) (andLeft hb) (andRight hb)
      · let B := InternalLessThan.strictLess k i ⊓ PreviousResult out i
        have hb : Nonempty (Derivation body (B :: A :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
        exact eraseAboveFromPrevious raw out d k i (withHyp (withHyp hr A) B) (andLeft hb) (andRight hb)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSpecProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSpecProof
