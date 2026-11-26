module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalBooleanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalDecisionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof
open InternalTagArithmeticSupportProof (symm)
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open InternalOriginalPairingOrderArithmeticProof (formulaCases withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderInternalBranchProof OriginalUniverseDecoderInternalBooleanProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem impApply {P Q : Formula alpha}
    (hi : Nonempty (Derivation body Delta (P.imp Q)))
    (hp : Nonempty (Derivation body Delta P)) : Nonempty (Derivation body Delta Q) := by
  obtain ⟨hi⟩ := hi
  obtain ⟨hp⟩ := hp
  exact ⟨Derivation.implicationElimination hi hp⟩

theorem contrapose {P Q : Formula alpha}
    (hi : Nonempty (Derivation body Delta (P.imp Q)))
    (hn : Nonempty (Derivation body Delta Q.not)) : Nonempty (Derivation body Delta P.not) := by
  obtain ⟨hi⟩ := withHyp hi P
  obtain ⟨hn⟩ := withHyp hn P
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination hn
      (Derivation.implicationElimination hi (Derivation.hypothesis List.mem_cons_self)))⟩

/-- All-output Boolean specification, using proved range and an internal
acceptance equivalence. This keeps zero and every impossible output explicit. -/
theorem decisionForward {n : Nat} {P : Program n} (tree : BooleanTree P)
    (out : OTerm alpha) (xs : Fin n → OTerm alpha) (C : Formula alpha)
    (hi : Nonempty (Derivation body Delta ((programGraph P (numeral 1) xs).iff C)))
    (ho : Nonempty (Derivation body Delta (programGraph P out xs))) :
    Nonempty (Derivation body Delta
      ((C ⊓ equal out (numeral 1)) ⊔ (C.not ⊓ equal out (numeral 0)))) := by
  apply formulaCases C _
  · have hc : Nonempty (Derivation body (C :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp := impApply (withHyp (andRight hi) C) hc
    have he : Nonempty (Derivation body (C :: Delta) (equal out (numeral 1))) := by
      simpa only [equalEqn] using valueUnique P out (numeral 1) xs (withHyp ho C) hp
    obtain ⟨h⟩ := andIntro hc he
    exact ⟨orLeft h⟩
  · have hc : Nonempty (Derivation body (C.not :: Delta) C.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp := booleanReject tree xs (contrapose (withHyp (andLeft hi) C.not) hc)
    have he : Nonempty (Derivation body (C.not :: Delta) (equal out (numeral 0))) := by
      simpa only [equalEqn] using valueUnique P out (numeral 0) xs (withHyp ho C.not) hp
    obtain ⟨h⟩ := andIntro hc he
    exact ⟨orRight h⟩

theorem decisionBackward {n : Nat} {P : Program n} (tree : BooleanTree P)
    (out : OTerm alpha) (xs : Fin n → OTerm alpha) (C : Formula alpha)
    (hi : Nonempty (Derivation body Delta ((programGraph P (numeral 1) xs).iff C)))
    (ho : Nonempty (Derivation body Delta
      ((C ⊓ equal out (numeral 1)) ⊔ (C.not ⊓ equal out (numeral 0))))) :
    Nonempty (Derivation body Delta (programGraph P out xs)) := by
  apply orCases ho
  · have hc : Nonempty (Derivation body ((C ⊓ equal out (numeral 1)) :: Delta)
        (C ⊓ equal out (numeral 1))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp := impApply (withHyp (andRight hi) _) (andLeft hc)
    obtain ⟨he⟩ := andRight hc
    exact outputTransport P (numeral 1) out xs
      ⟨symm (by simpa only [equalEqn] using he)⟩ hp
  · have hc : Nonempty (Derivation body ((C.not ⊓ equal out (numeral 0)) :: Delta)
        (C.not ⊓ equal out (numeral 0))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp := booleanReject tree xs (contrapose (withHyp (andLeft hi) _) (andLeft hc))
    obtain ⟨he⟩ := andRight hc
    exact outputTransport P (numeral 0) out xs
      ⟨symm (by simpa only [equalEqn] using he)⟩ hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalDecisionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalDecisionProof
