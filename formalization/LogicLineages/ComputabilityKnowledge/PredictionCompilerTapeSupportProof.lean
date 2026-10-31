module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerTapeSupportTargets
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerSupportProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerTapeSupportProof
open Turing Turing.ToPartrec Turing.PartrecToTM2 PredictionCompilerSupport PredictionCompilerTapeSupport
open PredictionCompilerTapeSupportTargets

private theorem symbols_all (s : Store) : s ∈ symbols := by
  cases s with | none => simp [symbols] | some a => cases a <;> simp [symbols]

theorem exactStackStatementEnumeration : ExactStackStatementEnumeration := by
  classical
  intro q
  induction q <;> intro l <;>
    simp_all [stackStatementList, TM2to1.trStmts₁, or_assoc, or_left_comm, or_comm]

private theorem stack_mem (q : StackStatement) (l : TapeLabel) :
    l ∈ stackStatementList q ↔ l ∈ TM2to1.trStmts₁ q := exactStackStatementEnumeration q l

private theorem source_mem (c : Code) (k : Cont') (l : Λ') :
    l ∈ supportList c k ↔ l ∈ codeSupp c k := by
  rw [← PredictionCompilerSupportProof.exactCompilerSupport c k]
  simp

theorem exactTapeLabelEnumeration : ExactTapeLabelEnumeration := by
  classical
  intro c k
  ext l
  simp [tapeLabels, TM2to1.trSupp, source_mem, stack_mem]

theorem exactTapeStatementEnumeration : ExactTapeStatementEnumeration := by
  classical
  intro q
  induction q <;> intro r <;>
    simp_all [tapeStatementList, TM1.stmts₁, or_assoc, or_left_comm, or_comm]

private theorem statement_mem (q r : TapeStatement) :
    r ∈ tapeStatementList q ↔ r ∈ TM1.stmts₁ q := exactTapeStatementEnumeration q r

set_option backward.isDefEq.respectTransparency false in
theorem exactPostLabelEnumeration : ExactPostLabelEnumeration := by
  classical
  letI : DecidableEq (Option TapeStatement × Store) := Classical.decEq _
  intro c k
  ext l
  rcases l with ⟨q, s⟩
  change (q, s) ∈ (postLabels c k).toFinset ↔
    (q, s) ∈ (TM1.stmts tapeMachine (tapeLabels c k).toFinset).product (Finset.univ : Finset Store)
  erw [Finset.mem_product]
  erw [List.mem_toFinset]
  cases q <;> simp [postLabels, tapeStatements, TM1.stmts, symbols_all, statement_mem,
    Finset.mem_insertNone, Finset.mem_biUnion, Prod.mk.injEq]

theorem actualTapeCompilerClosure : ActualTapeCompilerClosure := by
  classical
  intro c k
  letI : Inhabited Λ' := ⟨trNormal c k⟩
  rw [exactTapeLabelEnumeration c k]
  exact TM2to1.tr_supports tr (PartrecToTM2.tr_supports c k)

theorem actualPostCompilerClosure : ActualPostCompilerClosure := by
  classical
  intro c k
  letI : Inhabited Λ' := ⟨trNormal c k⟩
  have he : (↑(TM1to0.trStmts tapeMachine (tapeLabels c k).toFinset) : Set PostLabel) =
      {l | l ∈ postLabels c k} := by
    rw [← exactPostLabelEnumeration c k]
    ext l
    simp
  rw [← he]
  exact TM1to0.tr_supports tapeMachine (actualTapeCompilerClosure c k)

end LogicLineages.ComputabilityKnowledge.PredictionCompilerTapeSupportProof
