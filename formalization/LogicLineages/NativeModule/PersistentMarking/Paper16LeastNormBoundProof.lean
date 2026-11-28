module

public import LogicLineages.NativeModule.PersistentMarking.Paper16LeastNormBoundTargets
import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalIDStageProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusProof
import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLeastProof
import Mathlib.SetTheory.Cardinal.Regular

public section

namespace LogicLineages.PersistentMarking.Paper16LeastNormBoundProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus
open NumberedWindowExternalIDOperators NumberedWindowExternalIDStages
open ExternalOrdinalInterfaceID1Targets Paper16RemainingOrdinalTargets Paper16LeastNormBoundTargets
open Ordinal
open scoped Ordinal

theorem exact_StagesExhaustLeast : StagesExhaustLeast := by
  intro F mono n hn
  classical
  let U : Pred := fun m => ∃ a : Ordinal.{0}, a < ω₁ ∧ stage (· < ·) Ordinal.lt_wf F a m
  have prefixed : IsPrefixed F U := by
    intro m hm
    let g : Nat → Ordinal.{0} := fun k => if h : U k then Classical.choose h else 0
    have gSpec : ∀ k (h : U k), g k < ω₁ ∧ stage (· < ·) Ordinal.lt_wf F (g k) k := by
      intro k h
      have eq : g k = Classical.choose h := dif_pos h
      rw [eq]
      exact Classical.choose_spec h
    have gLt : ∀ k, g k < ω₁ := by
      intro k
      by_cases h : U k
      · exact (gSpec k h).1
      · have eq : g k = 0 := dif_neg h
        rw [eq]
        exact zero_lt_one.trans (one_lt_omega0.trans omega0_lt_omega_one)
    let top : Ordinal.{0} := Order.succ (⨆ k, g k)
    have topLt : top < ω₁ :=
      (Cardinal.isSuccLimit_omega 1).succ_lt (Ordinal.iSup_lt_omega_one gLt)
    have below : Below U (fun d => ∃ b, ∃ _ : b < top, stage (· < ·) Ordinal.lt_wf F b d) := by
      intro k hk
      exact ⟨g k, Order.lt_succ_of_le (Ordinal.le_iSup g k), (gSpec k hk).2⟩
    have stageTop : stage (· < ·) Ordinal.lt_wf F top m := by
      rw [NumberedWindowExternalIDStageProof.stageEq (· < ·) Ordinal.lt_wf F top]
      exact mono _ _ below m hm
    exact ⟨top, topLt, stageTop⟩
  exact hn U prefixed

theorem exact_BodyOperatorMonotone : BodyOperatorMonotone := by
  intro B P Q h n hn
  exact PositiveArithmeticOperatorsProof.positiveMonotonicity (Fin 1) B P Q h ![n] hn

theorem exact_DerivableAtomsHaveStages : DerivableAtomsHaveStages := by
  intro B n hd
  have truth : realize (standardLeastPredicate B)
      (Positive.predicate (α := Empty) (numeral n)).formula Empty.elim :=
    ID1Completion.InternalCalculusProof.actualInternalCalculusSoundness B (standardLeastPredicate B)
      (ID1Completion.InternalCalculusSupportProof.actualStandardLeastModel B) Empty []
      (Positive.predicate (α := Empty) (numeral n)).formula hd Empty.elim
      (by intro p hp; cases hp)
  rw [PositiveArithmeticOperatorsSupportProof.predicateTruth, numeralTruth] at truth
  have least : Least (bodyOperator B) n :=
    (NumberedWindowInternalLeastProof.interpretation B n).mp truth
  exact exact_StagesExhaustLeast (bodyOperator B) (exact_BodyOperatorMonotone B) n least

theorem exact_NormTheoremAtOmegaOne : NormTheoremAtOmegaOne := by
  intro B n hd
  exact exact_DerivableAtomsHaveStages B n hd

theorem exact_LeastNormBoundExists : LeastNormBoundExists := by
  have nonempty : {γ : Ordinal.{0} | NormTheorem γ}.Nonempty := ⟨ω₁, exact_NormTheoremAtOmegaOne⟩
  refine ⟨sInf {γ : Ordinal.{0} | NormTheorem γ}, ⟨csInf_mem nonempty, fun γ hγ => csInf_le' hγ⟩,
    csInf_le' exact_NormTheoremAtOmegaOne⟩

theorem exact_LeastNormBoundUnique : LeastNormBoundUnique := by
  intro β γ hβ hγ
  exact le_antisymm (hβ.2 γ hγ.1) (hγ.2 β hβ.1)

theorem exact_NormTheoremIffAbove : NormTheoremIffAbove := by
  intro β hβ γ
  constructor
  · exact hβ.2 γ
  · intro le B n hd
    obtain ⟨a, lt, staged⟩ := hβ.1 B n hd
    exact ⟨a, lt_of_lt_of_le lt le, staged⟩

#print axioms exact_StagesExhaustLeast
#print axioms exact_BodyOperatorMonotone
#print axioms exact_DerivableAtomsHaveStages
#print axioms exact_NormTheoremAtOmegaOne
#print axioms exact_LeastNormBoundExists
#print axioms exact_LeastNormBoundUnique
#print axioms exact_NormTheoremIffAbove

end LogicLineages.PersistentMarking.Paper16LeastNormBoundProof
