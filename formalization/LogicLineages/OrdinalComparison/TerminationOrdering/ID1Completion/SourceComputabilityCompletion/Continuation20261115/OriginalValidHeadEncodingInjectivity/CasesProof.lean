module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.CasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalHeadDecoderValidity.BackwardProof (orCases)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
def branch (i : Fin 6) (tag payload : OTerm alpha) : Formula alpha :=
  if i.val < 2 then eqn tag (numeral i.val) ⊓ eqn payload (numeral 0)
  else eqn tag (numeral i.val)
theorem invoke (tag payload : OTerm alpha) (C : Formula alpha)
    (next : ∀ i : Fin 6, Nonempty (Derivation body (branch i tag payload :: Delta) C))
    (i : Fin 6) (Theta : List (Formula alpha)) (inc : ∀ p ∈ Delta, p ∈ Theta)
    (hc : Nonempty (Derivation body Theta (branch i tag payload))) :
    Nonempty (Derivation body Theta C) := by
  obtain ⟨h⟩ := next i
  have hi : Nonempty (Derivation body Delta ((branch i tag payload).imp C)) :=
    ⟨Derivation.implicationIntroduction h⟩
  obtain ⟨hi⟩ := InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hi inc
  obtain ⟨hc⟩ := hc
  exact ⟨Derivation.implicationElimination hi hc⟩
theorem allowedElim (n : Nat) (tag payload : OTerm alpha) (C : Formula alpha)
    (ha : Nonempty (Derivation body Delta (OriginalHeadDecoderValidity.Targets.allowed n tag payload)))
    (next : ∀ i : Fin 6, Nonempty (Derivation body (branch i tag payload :: Delta) C)) :
    Nonempty (Derivation body Delta C) := by
  let B := (eqn tag (numeral 0) ⊔ eqn tag (numeral 1)) ⊓ eqn payload (numeral 0)
  let A5 := eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n)
  let A4 := eqn tag (numeral 4) ⊔ A5
  let A3 := eqn tag (numeral 3) ⊔ A4
  let A2 := eqn tag (numeral 2) ⊔ A3
  change Nonempty (Derivation body Delta (B ⊔ A2)) at ha
  apply orCases ha
  · have hb : Nonempty (Derivation body (B :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply orCases (andLeft hb)
    · apply invoke tag payload C next 0 _
      · intro q hq; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)
      · exact andIntro ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp (andRight hb) _)
    · apply invoke tag payload C next 1 _
      · intro q hq; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)
      · exact andIntro ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp (andRight hb) _)
  · have h2 : Nonempty (Derivation body (A2 :: Delta) A2) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply orCases h2
    · apply invoke tag payload C next 2 _
      · intro q hq; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)
      · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    · have h3 : Nonempty (Derivation body (A3 :: A2 :: Delta) A3) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      apply orCases h3
      · apply invoke tag payload C next 3 _
        · intro q hq; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
        · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
      · have h4 : Nonempty (Derivation body (A4 :: A3 :: A2 :: Delta) A4) := ⟨Derivation.hypothesis List.mem_cons_self⟩
        apply orCases h4
        · apply invoke tag payload C next 4 _
          · intro q hq; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)))
          · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
        · apply invoke tag payload C next 5 _
          · intro q hq; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)))
          · exact andLeft (show Nonempty (Derivation body (A5 :: A4 :: A3 :: A2 :: Delta) A5) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.CasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.CasesProof
