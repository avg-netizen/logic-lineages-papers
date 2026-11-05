module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadBooleanTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureDecisionSemanticInterface

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadBooleanProof
open CommonLayerSyntax CommonHeadBoolean

theorem exactTranslation : CommonHeadBooleanTargets.ExactTranslation := by
  intro Γ hg p ν
  induction p with
  | truth => rfl
  | falsity => rfl
  | equal a b =>
      change (CommonLayerComparison.compile (headCodes Γ) a b 0).eval ν ↔
        codedValue (headCodes Γ) a ν = codedValue (headCodes Γ) b ν
      rw [CommonHeadClosureDecisionSuppliers.codedComparison Γ hg a b 0 ν,
        Int.sign_eq_zero_iff_zero]
      omega
  | less a b =>
      change (CommonLayerComparison.compile (headCodes Γ) a b (-1)).eval ν ↔
        codedValue (headCodes Γ) a ν < codedValue (headCodes Γ) b ν
      rw [CommonHeadClosureDecisionSuppliers.codedComparison Γ hg a b (-1) ν,
        Int.sign_eq_neg_one_iff_neg]
      omega
  | negative p ih => exact not_congr ih
  | conjunction p q ihp ihq => exact and_congr ihp ihq
  | disjunction p q ihp ihq => exact or_congr ihp ihq

theorem exactPrefixTranslation : CommonHeadBooleanTargets.ExactPrefixTranslation := by
  intro Γ hg xs p ν
  induction xs generalizing ν with
  | nil => exact ⟨exactTranslation Γ hg p ν, exactTranslation Γ hg p ν⟩
  | cons i xs ih =>
      exact ⟨exists_congr (fun n => (ih (Function.update ν i n)).1),
        forall_congr' (fun n => (ih (Function.update ν i n)).2)⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadBooleanProof
