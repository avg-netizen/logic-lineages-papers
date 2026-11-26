module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalDecisionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalSwitchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSupportProof (refl)
open InternalTagArithmeticSyntaxProof (eqn)
open InternalOriginalPairingOrderArithmeticProof (withHyp)
open OriginalLambdaConstructorGraphSyntaxProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSelectorBoundsProof (numeralRelabel)
open OriginalTypedDecoder (ifSame)
open OriginalTypedDecoderInternalBranchProof OriginalUniverseDecoderInternalBooleanProof
open OriginalUniverseDecoderInternalDecisionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem valueNotOne {n : Nat} (test : Program n) (v : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hv : Nonempty (Derivation body Delta (programGraph test v xs)))
    (hn : Nonempty (Derivation body Delta (programGraph test (numeral 1) xs).not)) :
    Nonempty (Derivation body Delta (equal v (numeral 1)).not) := by
  have he : Nonempty (Derivation body (equal v (numeral 1) :: Delta) (equal v (numeral 1))) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hp⟩ := outputTransport (Gamma := equal v (numeral 1) :: Delta) test v (numeral 1) xs
    (by simpa only [equalEqn] using he) (withHyp hv _)
  obtain ⟨hn⟩ := withHyp hn (equal v (numeral 1))
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn hp)⟩

theorem exactOneNoElim {n : Nat} (test yes no : Program n) (out : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hn : Nonempty (Derivation body Delta (programGraph test (numeral 1) xs).not))
    (ho : Nonempty (Derivation body Delta
      (programGraph (ifSame test (constant n 1) yes no) out xs))) :
    Nonempty (Derivation body Delta (programGraph no out xs)) := by
  apply programCases test xs _
  intro beta j Theta v hj hv
  have hn' := renameInto hn j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [notRename,programRename,numeralRelabel] at hn' ho' ⊢
  let xx := fun i => (xs i).relabel j
  exact sameNoElim test (constant n 1) yes no (out.relabel j) v (numeral 1) xx hv
    (constantValue 1 xx) (valueNotOne test v xx hv hn') ho'

theorem exactOneNoIntro {n : Nat} (test yes no : Program n) (out : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hn : Nonempty (Derivation body Delta (programGraph test (numeral 1) xs).not))
    (ho : Nonempty (Derivation body Delta (programGraph no out xs))) :
    Nonempty (Derivation body Delta
      (programGraph (ifSame test (constant n 1) yes no) out xs)) := by
  apply programCases test xs _
  intro beta j Theta v hj hv
  have hn' := renameInto hn j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [notRename,programRename,numeralRelabel] at hn' ho' ⊢
  let xx := fun i => (xs i).relabel j
  exact sameNoIntro test (constant n 1) yes no (out.relabel j) v (numeral 1) xx hv
    (constantValue 1 xx) (valueNotOne test v xx hv hn') ho'

theorem exactOneYesElim {n : Nat} (test yes no : Program n) (out : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph test (numeral 1) xs)))
    (ho : Nonempty (Derivation body Delta
      (programGraph (ifSame test (constant n 1) yes no) out xs))) :
    Nonempty (Derivation body Delta (programGraph yes out xs)) :=
  sameYesElim test (constant n 1) yes no out (numeral 1) (numeral 1) xs ht (constantValue 1 xs)
    (by simpa only [equalEqn] using (show Nonempty (Derivation body Delta (eqn (numeral 1 : OTerm alpha) (numeral 1))) from ⟨refl _⟩)) ho

theorem exactOneYesIntro {n : Nat} (test yes no : Program n) (out : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph test (numeral 1) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph yes out xs))) :
    Nonempty (Derivation body Delta
      (programGraph (ifSame test (constant n 1) yes no) out xs)) :=
  sameYesIntro test (constant n 1) yes no out (numeral 1) (numeral 1) xs ht (constantValue 1 xs)
    (by simpa only [equalEqn] using (show Nonempty (Derivation body Delta (eqn (numeral 1 : OTerm alpha) (numeral 1))) from ⟨refl _⟩)) ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalSwitchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalSwitchProof
