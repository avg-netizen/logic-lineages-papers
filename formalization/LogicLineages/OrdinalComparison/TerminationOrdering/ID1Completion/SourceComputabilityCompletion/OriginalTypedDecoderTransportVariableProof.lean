module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportVariableSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportVariableProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalTagArithmeticSyntaxProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalFiniteBlocksSubstitutionProof (renameIdentity)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalContextInsertionVariableSupportProof (withHyp)
open OriginalVariableDecoderGraphSupportProof (graphRename)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open OriginalRawSyntaxTransportInternalVariableSpecSyntaxProof
open OriginalRawSyntaxTransportInternalVariableActionProof
open OriginalTypedDecoderTransport OriginalTypedDecoderTransportVariableSupportProof

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

@[simp] theorem sourceContextRename {beta : Type} (erasing : Bool)
    (gamma extended : OTerm alpha) (j : alpha → beta) :
    (sourceContext erasing gamma extended).relabel j =
      sourceContext erasing (gamma.relabel j) (extended.relabel j) := by
  cases erasing <;> rfl

@[simp] theorem targetContextRename {beta : Type} (erasing : Bool)
    (gamma extended : OTerm alpha) (j : alpha → beta) :
    (targetContext erasing gamma extended).relabel j =
      targetContext erasing (gamma.relabel j) (extended.relabel j) := by
  cases erasing <;> rfl

/-- The actual original variable action transports an accepted original
variable to an accepted variable in the target context, or to literal bottom
at the SAME requested type. Existential predecessor witnesses are supplied
internally and eliminated through the callback. No type-window premise occurs. -/
theorem variableTransport (erasing : Bool)
    (out d cutoff typ index gamma extended : OTerm alpha) (psi : Formula alpha)
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (hv : Nonempty (Derivation body Delta
      (OriginalVariableDecoder.graph (numeral 1) typ index (sourceContext erasing gamma extended))))
    (ha : Nonempty (Derivation body Delta
      (graph3 (variableAction (selectedMode erasing)) out d cutoff index)))
    (kvariable : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (targetIndex : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 variableConstructor (out.relabel j) targetIndex)) →
      Nonempty (Derivation body Theta
        (OriginalVariableDecoder.graph (numeral 1) (typ.relabel j) targetIndex
          ((targetContext erasing gamma extended).relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j)))
    (kbottom : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph1 bottomConstructor (out.relabel j) (typ.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  have variableSame (Theta : List (Formula alpha)) (targetIndex : OTerm alpha)
      (hj : ∀ p ∈ Delta, p ∈ Theta)
      (hc : Nonempty (Derivation body Theta (graph1 variableConstructor out targetIndex)))
      (ht : Nonempty (Derivation body Theta
        (OriginalVariableDecoder.graph (numeral 1) typ targetIndex
          (targetContext erasing gamma extended)))) :
      Nonempty (Derivation body Theta psi) := by
    have h := kvariable alpha id Theta targetIndex
      (fun p hp => by simpa only [renameIdentity] using hj p hp)
      (by simpa only [Term.relabel_id] using hc)
      (by simpa only [Term.relabel_id] using ht)
    simpa only [renameIdentity] using h
  have bottomSame (Theta : List (Formula alpha))
      (hj : ∀ p ∈ Delta, p ∈ Theta)
      (hc : Nonempty (Derivation body Theta (graph1 bottomConstructor out typ))) :
      Nonempty (Derivation body Theta psi) := by
    have h := kbottom alpha id Theta
      (fun p hp => by simpa only [renameIdentity] using hj p hp)
      (by simpa only [Term.relabel_id] using hc)
    simpa only [renameIdentity] using h
  have hs := variableActionSpecForward (selectedMode erasing) out d cutoff index ha
  cases erasing with
  | false =>
    change Nonempty (Derivation body Delta
      ((Below index cutoff ⊓ graph1 variableConstructor out index) ⊔
        ((Below index cutoff).not ⊓ graph1 variableConstructor out (suc index)))) at hs
    apply orCases hs
    · let A := Below index cutoff ⊓ graph1 variableConstructor out index
      have h : Nonempty (Derivation body (A :: Delta) A) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact variableSame (A :: Delta) index (fun _ hp => List.mem_cons_of_mem A hp)
        (andRight h) (shiftBelow typ index d cutoff gamma extended
          (withHyp hi A) (andLeft h) (withHyp hv A))
    · let A := (Below index cutoff).not ⊓ graph1 variableConstructor out (suc index)
      have h : Nonempty (Derivation body (A :: Delta) A) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact variableSame (A :: Delta) (suc index) (fun _ hp => List.mem_cons_of_mem A hp)
        (andRight h) (shiftAbove typ index d cutoff gamma extended
          (withHyp hi A) (andLeft h) (withHyp hv A))
  | true =>
    change Nonempty (Derivation body Delta
      ((Below index cutoff ⊓ graph1 variableConstructor out index) ⊔
        ((equal index cutoff ⊓ graph1 bottomConstructor out d) ⊔
          (Below cutoff index ⊓ PreviousResult out index)))) at hs
    apply orCases hs
    · let A := Below index cutoff ⊓ graph1 variableConstructor out index
      have h : Nonempty (Derivation body (A :: Delta) A) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact variableSame (A :: Delta) index (fun _ hp => List.mem_cons_of_mem A hp)
        (andRight h) (eraseBelow typ index d cutoff gamma extended
          (withHyp hi A) (andLeft h) (withHyp hv A))
    · let A := (equal index cutoff ⊓ graph1 bottomConstructor out d) ⊔
        (Below cutoff index ⊓ PreviousResult out index)
      have h : Nonempty (Derivation body (A :: Delta) A) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      apply orCases h
      · let B := equal index cutoff ⊓ graph1 bottomConstructor out d
        have h' : Nonempty (Derivation body (B :: A :: Delta) B) :=
          ⟨Derivation.hypothesis List.mem_cons_self⟩
        exact bottomSame (B :: A :: Delta)
          (fun _ hp => List.mem_cons_of_mem B (List.mem_cons_of_mem A hp))
          (eraseAt out typ index d cutoff gamma extended
            (withHyp (withHyp hi A) B) (andLeft h')
            (withHyp (withHyp hv A) B) (andRight h'))
      · let B := Below cutoff index ⊓ PreviousResult out index
        have h' : Nonempty (Derivation body (B :: A :: Delta) B) :=
          ⟨Derivation.hypothesis List.mem_cons_self⟩
        apply previousCases out index psi (andRight h')
        intro beta j Theta previous hj hp hc
        have hi' := renameInto (withHyp (withHyp hi A) B) j Theta hj
        rw [insertRename] at hi'
        have hv' := renameInto (withHyp (withHyp hv A) B) j Theta hj
        change Nonempty (Derivation body Theta
          ((OriginalVariableDecoder.graph (numeral 1) typ index extended).relabel j)) at hv'
        simp only [graphRename,numeral,sucRelabel,zRelabel] at hv'
        have hg' := renameInto (andLeft h') j Theta hj
        change Nonempty (Derivation body Theta ((ltF cutoff index).relabel j)) at hg'
        rw [orderRename] at hg'
        exact kvariable beta j Theta previous
          (fun p hp' => hj p (List.mem_cons_of_mem B (List.mem_cons_of_mem A hp')))
          hc (eraseAbove (typ.relabel j) (index.relabel j) previous (d.relabel j)
            (cutoff.relabel j) (gamma.relabel j) (extended.relabel j) hi' hg' hp hv')

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportVariableProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportVariableProof
