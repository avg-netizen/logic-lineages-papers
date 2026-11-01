module
public import LogicLineages.OrdinalComparison.OneInputBooleanProgramProof
public import LogicLineages.OrdinalComparison.ComparisonNodeTailProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.OneInputBoolean

theorem tail_positive (program : List OneInputBooleanInstruction) : 1≤encodedOneInputBooleanTail program := by
  induction program with
  | nil => exact le_rfl
  | cons instruction rest ih => exact ih.trans (Nat.le_max_right _ _)

theorem tail_member (program : List OneInputBooleanInstruction) (instruction : OneInputBooleanInstruction)
    (hm : instruction∈program) : encodedOneInputBooleanInstructionTail instruction≤encodedOneInputBooleanTail program := by
  induction program with
  | nil => cases hm
  | cons item rest ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact Nat.le_max_left _ _
    · exact (ih hm).trans (Nat.le_max_right _ _)

theorem tail_le (program : List OneInputBooleanInstruction) (N : Nat) (hN : 1≤N)
    (h : ∀ instruction∈program,encodedOneInputBooleanInstructionTail instruction≤N) :
    encodedOneInputBooleanTail program≤N := by
  induction program with
  | nil => exact hN
  | cons item rest ih =>
    apply Nat.max_le.mpr
    exact ⟨h item List.mem_cons_self,ih (fun i hi => h i (List.mem_cons_of_mem _ hi))⟩

theorem subprogram_tail (part whole : List OneInputBooleanInstruction)
    (h : ∀ instruction∈part,instruction∈whole) : encodedOneInputBooleanTail part≤encodedOneInputBooleanTail whole :=
  tail_le part _ (tail_positive whole) (fun instruction hm => tail_member whole instruction (h instruction hm))

theorem atom_bound (relation : OneInputOrderRelation) (E F : FixedLimitPositiveExpr) :
    (encodedOneVariableSignDecision (2*positiveExprEncode E) (2*positiveExprEncode F)).2≤
      encodedOneInputBooleanTail (oneInputBooleanCompile (.atom relation E F)) := by
  have hh := tail_member (oneInputBooleanCompile (.atom relation E F))
    (2+oneInputOrderRelationCode relation,positiveExprEncode E,positiveExprEncode F) (List.mem_singleton_self _)
  cases relation <;>
    simpa [oneInputOrderRelationCode,encodedOneInputBooleanInstructionTail] using hh

private theorem order_stable (r : OneInputOrderRelation) (a b c d : Nat)
    (he : a=b ↔ c=d) (hle : a≤b ↔ c≤d) (hlt : a<b ↔ c<d) :
    oneInputOrderBool (oneInputOrderRelationCode r) a b=
      oneInputOrderBool (oneInputOrderRelationCode r) c d := by
  cases r <;> simp [oneInputOrderBool,oneInputOrderRelationCode,he,hle,hlt]

theorem atom_stable (relation : OneInputOrderRelation) (E F : FixedLimitPositiveExpr)
    (hE : fixedLimitProfileBelow epsilonZero E) (hF : fixedLimitProfileBelow epsilonZero F)
    (x y : Nat)
    (hx : (encodedOneVariableSignDecision (2*positiveExprEncode E) (2*positiveExprEncode F)).2≤x)
    (hy : (encodedOneVariableSignDecision (2*positiveExprEncode E) (2*positiveExprEncode F)).2≤y) :
    actualOneInputBooleanValue (.atom relation E F) x=actualOneInputBooleanValue (.atom relation E F) y := by
  have hData := (ComparisonAssembly.result_correct
    ((oneVariableComparisonEncode (.positive E),oneVariableComparisonEncode (.positive F)),(1,1))
    (.positive E) (.positive F) rfl rfl hE hF).1
  have hx' : (encodedComparisonQueryResult
      ((oneVariableComparisonEncode (.positive E),oneVariableComparisonEncode (.positive F)),(1,1))).2≤x := hx
  have hy' : (encodedComparisonQueryResult
      ((oneVariableComparisonEncode (.positive E),oneVariableComparisonEncode (.positive F)),(1,1))).2≤y := hy
  have he : actualFixedLimitProfileEval E x=actualFixedLimitProfileEval F x ↔
      actualFixedLimitProfileEval E y=actualFixedLimitProfileEval F y :=
    (hData.2.2 x hx').2.2.2.1.symm.trans (hData.2.2 y hy').2.2.2.1
  have hlt : actualFixedLimitProfileEval E x<actualFixedLimitProfileEval F x ↔
      actualFixedLimitProfileEval E y<actualFixedLimitProfileEval F y :=
    (hData.2.2 x hx').2.2.1.symm.trans (hData.2.2 y hy').2.2.1
  have hle := ComparisonNode.weak_order_stable _ _ _ hData x y hx' hy'
  exact order_stable relation _ _ _ _ he hle hlt

theorem formula_stable (formula : OneInputBooleanExpr) (hv : oneInputBooleanValid formula)
    (N : Nat) (hCut : encodedOneInputBooleanTail (oneInputBooleanCompile formula)≤N)
    (x y : Nat) (hx : N≤x) (hy : N≤y) :
    actualOneInputBooleanValue formula x=actualOneInputBooleanValue formula y := by
  induction formula with
  | truth value => rfl
  | atom relation E F =>
    exact atom_stable relation E F hv.1 hv.2 x y ((atom_bound relation E F).trans (hCut.trans hx))
      ((atom_bound relation E F).trans (hCut.trans hy))
  | neg formula ih =>
    have hSub : encodedOneInputBooleanTail (oneInputBooleanCompile formula)≤N := by
      apply le_trans (subprogram_tail _ _ ?_) hCut
      intro instruction hm
      exact List.mem_append_left _ hm
    exact congrArg Bool.not (ih hv hSub)
  | conj left right ihL ihR =>
    have hLeft : encodedOneInputBooleanTail (oneInputBooleanCompile left)≤N := by
      apply le_trans (subprogram_tail _ _ ?_) hCut
      intro instruction hm
      exact List.mem_append_left _ (List.mem_append_left _ hm)
    have hRight : encodedOneInputBooleanTail (oneInputBooleanCompile right)≤N := by
      apply le_trans (subprogram_tail _ _ ?_) hCut
      intro instruction hm
      exact List.mem_append_left _ (List.mem_append_right _ hm)
    exact congrArg₂ Bool.and (ihL hv.1 hLeft) (ihR hv.2 hRight)
  | disj left right ihL ihR =>
    have hLeft : encodedOneInputBooleanTail (oneInputBooleanCompile left)≤N := by
      apply le_trans (subprogram_tail _ _ ?_) hCut
      intro instruction hm
      exact List.mem_append_left _ (List.mem_append_left _ hm)
    have hRight : encodedOneInputBooleanTail (oneInputBooleanCompile right)≤N := by
      apply le_trans (subprogram_tail _ _ ?_) hCut
      intro instruction hm
      exact List.mem_append_left _ (List.mem_append_right _ hm)
    exact congrArg₂ Bool.or (ihL hv.1 hLeft) (ihR hv.2 hRight)

theorem source_tail : Targets.ActualOneInputBooleanTail := by
  intro formula hv
  refine ⟨tail_positive _,?_⟩
  intro x hx
  exact formula_stable formula hv _ le_rfl x _ hx le_rfl

end LogicLineages.OrdinalComparison.OneInputBoolean
