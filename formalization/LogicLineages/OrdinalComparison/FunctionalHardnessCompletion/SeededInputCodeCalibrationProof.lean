module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededInputCodeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededInputCode.Proof
open SignedPair
open SeededSourceCode (expressionCode)

private theorem shift_iterate {n : Nat} (k : Nat) (a : Expression n) :
    (shiftCode^[k]) (expressionCode a) = expressionCode ((Expression.shift^[k]) a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      rfl

private theorem repeat_correct {n : Nat} (a : Expression n) (k : Nat) :
    repeatCode (expressionCode a) k = expressionCode (repeatExpression a k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (addCode (expressionCode a))^[k+1] zeroCode = _
      rw [Function.iterate_succ_apply']
      change addCode (expressionCode a) (repeatCode (expressionCode a) k) = _
      rw [ih]
      rfl

private theorem expand_body_correct {n : Nat} (c : Int) (p : Nat) (a : Expression n) :
    (if c < 0 then negateCode (repeatCode ((shiftCode^[p]) (expressionCode a)) c.natAbs)
      else repeatCode ((shiftCode^[p]) (expressionCode a)) c.natAbs) =
      expressionCode (if c < 0 then .neg (repeatExpression ((Expression.shift^[p]) a) c.natAbs)
        else repeatExpression ((Expression.shift^[p]) a) c.natAbs) := by
  rw [shift_iterate, repeat_correct]
  split_ifs <;> rfl

private theorem expand_correct {n : Nat} (m : Monomial n) :
    expandMonomial (m.coefficient, m.power, m.unknown.map Fin.val) =
      expressionCode (monomialExpression m) := by
  rcases m with ⟨c, p, u⟩
  cases u with
  | none => exact expand_body_correct c p (Expression.unit : Expression n)
  | some i => exact expand_body_correct c p (.var i)

theorem exactMonomialCode : Targets.ExactMonomialCode := by
  intro n m
  rcases m with ⟨c, p, u⟩
  cases u with
  | none =>
      change some (expandMonomial (c, p, none)) =
        some (expressionCode (monomialExpression (⟨c, p, none⟩ : Monomial n)))
      exact congrArg some (expand_correct (⟨c, p, none⟩ : Monomial n))
  | some i =>
      by_cases hi : i < n
      · simp only [monomialCode, validMonomial, monomialOfCode, hi, decide_true,
          ↓reduceIte, ↓reduceDIte, Option.map_some]
        exact congrArg some (expand_correct (⟨c, p, some ⟨i, hi⟩⟩ : Monomial n))
      · simp [monomialCode, validMonomial, monomialOfCode, hi]

theorem exactRows : Targets.ExactRows := by
  intro n row
  induction row with
  | nil => rfl
  | cons m row ih =>
      change (match monomialCode n m with
        | none => rowCode n row | some b => addCode b (rowCode n row)) = _
      rw [exactMonomialCode, ih]
      cases h : monomialOfCode n m <;>
        simp [h, fromMonomials, expressionCode, addCode]

private theorem mod_tag (a tag : Nat) (h : tag < 6) : (6 * a + tag) % 6 = tag := by omega
private theorem div_tag (a tag : Nat) (h : tag < 6) : (6 * a + tag) / 6 = a := by omega

theorem exactSubtractSeed : Targets.ExactSubtractSeed := by
  intro n d
  induction d with
  | unit => rw [expressionCode, subtractSeedCode]; rfl
  | var i =>
      rw [expressionCode, subtractSeedCode]
      simp [mod_tag _ 1 (by decide), div_tag _ 1 (by decide),
        SeededCompiler.subtractSeed, expressionCode, addCode, variableCode, negateCode]
  | add a b iha ihb =>
      rw [expressionCode, subtractSeedCode]
      simp [mod_tag _ 2 (by decide), div_tag _ 2 (by decide), Nat.unpair_pair,
        iha, ihb, SeededCompiler.subtractSeed, expressionCode, addCode]
  | neg a ih =>
      rw [expressionCode, subtractSeedCode]
      simp [mod_tag _ 3 (by decide), div_tag _ 3 (by decide),
        ih, SeededCompiler.subtractSeed, expressionCode, negateCode]
  | shift a ih =>
      rw [expressionCode, subtractSeedCode]
      simp [mod_tag _ 4 (by decide), div_tag _ 4 (by decide),
        ih, SeededCompiler.subtractSeed, expressionCode, shiftCode]

theorem exactSystemInputs : Targets.ExactSystemInputs := by
  intro c
  have hi : inputCode c = (systemOfCode c).map expressionCode := by
    simp only [inputCode, systemOfCode, List.map_map]
    exact List.map_congr_left (fun _ _ => exactRows c.1 _)
  refine ⟨hi, ?_⟩
  rw [seededInputCode, hi, List.map_map]
  exact List.map_congr_left (fun _ _ => exactSubtractSeed c.1 _)

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededInputCode.Proof
