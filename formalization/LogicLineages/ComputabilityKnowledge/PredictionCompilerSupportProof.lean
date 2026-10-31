module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerSupportTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerSupportProof
open Turing Turing.ToPartrec Turing.PartrecToTM2 PredictionCompilerSupport PredictionCompilerSupportTargets

private theorem symbols_all (s : Option Γ') : s ∈ symbols := by
  cases s with
  | none => simp [symbols]
  | some a => cases a <;> simp [symbols]

theorem exactLabelEnumeration : ExactLabelEnumeration := by
  intro q
  induction q <;> intro x <;>
    simp_all [labelList, trStmts₁, symbols_all, or_assoc, or_left_comm, or_comm]

private theorem label_mem (q x : Λ') : x ∈ labelList q ↔ x ∈ trStmts₁ q :=
  exactLabelEnumeration q x

theorem exactBodyEnumeration : ExactBodyEnumeration := by
  intro c
  induction c <;> intro k x <;>
    simp_all [bodyList, codeSupp', label_mem, or_assoc, or_left_comm, or_comm]

private theorem body_mem (c : Code) (k : Cont') (x : Λ') :
    x ∈ bodyList c k ↔ x ∈ codeSupp' c k := exactBodyEnumeration c k x

theorem exactContinuationEnumeration : ExactContinuationEnumeration := by
  intro k
  induction k <;> intro x <;>
    simp_all [continuationList, contSupp, body_mem, label_mem, or_assoc, or_left_comm, or_comm]

private theorem continuation_mem (k : Cont') (x : Λ') :
    x ∈ continuationList k ↔ x ∈ contSupp k := exactContinuationEnumeration k x

theorem exactCompilerSupport : ExactCompilerSupport := by
  intro c k
  ext x
  simp [supportList, codeSupp, body_mem, continuation_mem]

theorem actualCompilerClosure : ActualCompilerClosure := by
  intro c k
  rw [exactCompilerSupport c k]
  exact tr_supports c k

end LogicLineages.ComputabilityKnowledge.PredictionCompilerSupportProof
