module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.ClauseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalHeadDecoderValidity.BackwardProof (orCases)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem reject (actual expected : Nat) (hne : actual ≠ expected) (C : Formula alpha)
    (h : Nonempty (Derivation body Delta (eqn (numeral actual) (numeral expected)))) :
    Nonempty (Derivation body Delta C) := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.explosion (OriginalRawSyntaxTransportInternalConstructorSupportProof.numeralNeApply actual expected hne h)⟩

theorem headFromAllowed (n : Nat) (numbered : Bool) (payload first second head : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (OriginalCodeValidityConstructors.Targets.allowed n
      (numeral (if numbered then 5 else 4)) payload first second head))) :
    Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head)) := by
  let tag := numeral (if numbered then 5 else 4) (alpha := alpha)
  let H := graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head
  let F := graph1 (OriginalCodeValidityGuard.check n) (numeral 1) first
  let S := graph1 (OriginalCodeValidityGuard.check n) (numeral 1) second
  let C0 := eqn tag (numeral 0) ⊔ eqn tag (numeral 3)
  let C1 := eqn tag (numeral 1) ⊓ F
  let C2 := (eqn tag (numeral 2) ⊔ eqn tag (numeral 7)) ⊓ (F ⊓ S)
  let C4 := eqn tag (numeral 4) ⊓ (H ⊓ F)
  let C5 := eqn tag (numeral 5) ⊓ ((H ⊓ F) ⊓ S)
  let C6 := eqn tag (numeral 6) ⊓ eqn payload (numeral 0)
  let R5 := C5 ⊔ C6
  let R4 := C4 ⊔ R5
  let R2 := C2 ⊔ R4
  let R1 := C1 ⊔ R2
  change Nonempty (Derivation body Delta (C0 ⊔ R1)) at ha
  apply orCases ha
  · have h0 : Nonempty (Derivation body (C0 :: Delta) C0) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply orCases h0
    · exact reject (if numbered then 5 else 4) 0 (by cases numbered <;> decide) H ⟨Derivation.hypothesis List.mem_cons_self⟩
    · exact reject (if numbered then 5 else 4) 3 (by cases numbered <;> decide) H ⟨Derivation.hypothesis List.mem_cons_self⟩
  · have h1 : Nonempty (Derivation body (R1 :: Delta) R1) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply orCases h1
    · have hc : Nonempty (Derivation body (C1 :: R1 :: Delta) C1) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact reject (if numbered then 5 else 4) 1 (by cases numbered <;> decide) H (andLeft hc)
    · have h2 : Nonempty (Derivation body (R2 :: R1 :: Delta) R2) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      apply orCases h2
      · have hc : Nonempty (Derivation body (C2 :: R2 :: R1 :: Delta) C2) := ⟨Derivation.hypothesis List.mem_cons_self⟩
        apply orCases (andLeft hc)
        · exact reject (if numbered then 5 else 4) 2 (by cases numbered <;> decide) H ⟨Derivation.hypothesis List.mem_cons_self⟩
        · exact reject (if numbered then 5 else 4) 7 (by cases numbered <;> decide) H ⟨Derivation.hypothesis List.mem_cons_self⟩
      · have h4 : Nonempty (Derivation body (R4 :: R2 :: R1 :: Delta) R4) := ⟨Derivation.hypothesis List.mem_cons_self⟩
        apply orCases h4
        · have hc : Nonempty (Derivation body (C4 :: R4 :: R2 :: R1 :: Delta) C4) := ⟨Derivation.hypothesis List.mem_cons_self⟩
          exact andLeft (andRight hc)
        · have h5 : Nonempty (Derivation body (R5 :: R4 :: R2 :: R1 :: Delta) R5) := ⟨Derivation.hypothesis List.mem_cons_self⟩
          apply orCases h5
          · have hc : Nonempty (Derivation body (C5 :: R5 :: R4 :: R2 :: R1 :: Delta) C5) := ⟨Derivation.hypothesis List.mem_cons_self⟩
            exact andLeft (andLeft (andRight hc))
          · have hc : Nonempty (Derivation body (C6 :: R5 :: R4 :: R2 :: R1 :: Delta) C6) := ⟨Derivation.hypothesis List.mem_cons_self⟩
            exact reject (if numbered then 5 else 4) 6 (by cases numbered <;> decide) H (andLeft hc)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.ClauseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.ClauseProof
