module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompilerTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescentCodeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompiler.Proof

private theorem base_encode (E F : CommonLayerSyntax.BaseTerm) (desired : Int) :
    baseCode E.encode F.encode desired = (baseFormula E F desired).encode := by
  unfold baseCode baseFormula
  split_ifs <;> rfl

/-- The literal BASE leaf is calibrated under every original raw valuation,
including all desired integers outside the three possible signs. -/
private theorem base_eval (E F : CommonLayerSyntax.BaseTerm) (desired : Int)
    (ν : Nat → Nat) :
    (baseFormula E F desired).eval ν ↔
      Int.sign ((E.value ν : Int) - (F.value ν : Int)) = desired := by
  by_cases hz : desired = 0
  · subst desired
    simp only [baseFormula, ↓reduceIte, BaseFormula.Formula.eval,
      Int.sign_eq_zero_iff_zero]
    omega
  · by_cases hn : desired = -1
    · subst desired
      simp only [baseFormula, hz, ↓reduceIte, BaseFormula.Formula.eval,
        Int.sign_eq_neg_one_iff_neg]
      omega
    · by_cases hp : desired = 1
      · subst desired
        simp only [baseFormula, hz, hn, ↓reduceIte, BaseFormula.Formula.eval,
          Int.sign_eq_one_iff_pos]
        omega
      · simp only [baseFormula, hz, hn, hp, ↓reduceIte,
          BaseFormula.Formula.eval, false_iff]
        intro h
        rcases Int.sign_trichotomy ((E.value ν : Int) - (F.value ν : Int)) with hs | hs | hs
        · exact hp (h.symm.trans hs)
        · exact hz (h.symm.trans hs)
        · exact hn (h.symm.trans hs)

private theorem child_certificate (Γ : List Nat) (C : Nat) (labels : List Nat)
    (q : CommonHeadCompiler.Instruction) :
    (BalancedGuardDescent.child Γ C labels q).2.1 = C := by
  unfold BalancedGuardDescent.child
  split_ifs <;> rfl

private theorem source_child_parameters (k : Nat) (Γ : List Nat) (C E F : Nat)
    (desired : Int) (a : Input)
    (ha : a ∈ BalancedGuardDescent.sourceChildren k Γ C E F desired) :
    a.1 = Γ ∧ a.2.1 = BalancedSourceAdapter.lowerCertificate C := by
  unfold BalancedGuardDescent.sourceChildren BalancedGuardDescent.children at ha
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
  exact ⟨BalancedGuardDescent.Proof.child_shape Γ _ _ q,
    child_certificate Γ _ _ q⟩

private theorem strict_descent (a b : Input) (hb : b ∈ children a) :
    measure b < measure a := by
  rcases a with ⟨Γ, C, E, F, desired⟩
  cases Γ with
  | nil => simp only [children, List.not_mem_nil] at hb
  | cons k Γ =>
    exact (BalancedGuardDescent.Proof.exactActualCallsAndDescent.1 k Γ C E F desired).2 b hb

/-- The recursive call really consumes each child's own shape. Its equality
with Γ follows from the actual source child list, not a supplied callback law. -/
private theorem recursive_equation (a : Input) :
    recursiveCode a = assemble a ((children a).map recursiveCode) := by
  rcases a with ⟨Γ, C, E, F, desired⟩
  cases Γ with
  | nil => rfl
  | cons k Γ =>
    have hm :
        (BalancedGuardDescent.sourceChildren k Γ C E F desired).map
            (fun b => compileCode Γ b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2) =
          (BalancedGuardDescent.sourceChildren k Γ C E F desired).map recursiveCode := by
      apply List.map_congr_left
      intro b hb
      unfold recursiveCode
      rw [(source_child_parameters k Γ C E F desired b hb).1]
    exact congrArg (fun results => CommonHeadCode.disjunction
      (BalancedBoxFormula.formulaCode k Γ C E F desired)
      (BalancedGuardDescent.sourceAssemble k E F desired results)) hm

theorem exactFiniteCallEquation : Targets.ExactFiniteCallEquation := by
  refine ⟨?_, ?_, ?_, strict_descent, recursive_equation⟩
  · intro C E F desired
    rfl
  · intro C E F desired
    exact ⟨base_encode E F desired, base_eval E F desired⟩
  · intro k Γ C E F desired
    refine ⟨(BalancedGuardDescent.Proof.exactActualCallsAndDescent.1 k Γ C E F desired).1, ?_⟩
    intro a ha
    exact source_child_parameters k Γ C E F desired a ha

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompiler.Proof
