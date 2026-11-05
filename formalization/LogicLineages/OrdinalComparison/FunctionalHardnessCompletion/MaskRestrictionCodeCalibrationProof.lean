module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.MaskRestrictionCodeTargets
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.PatternProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.MaskRestrictionCode.Proof
open SignedPair
open SeededSourceCode (expressionCode)

private theorem mask_cases {n : Nat} (b : Bool) (z : Mask n) :
    maskCode (Fin.cases b z) = b :: maskCode z := by
  simp [maskCode, List.ofFn_succ]

private theorem masks_correct (n : Nat) : masksCode n = (masks n).map maskCode := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [masksCode, ih, masks, extendMasks, List.map_flatMap, List.flatMap_map, mask_cases]

theorem exactMasks : Targets.ExactMasks := by
  intro n
  have hc := masks_correct n
  refine ⟨hc, ?_, ?_⟩
  · rw [hc, List.length_map]
    exact (FunctionalHardnessCompletion.Proof.completePatterns n).1
  · intro z
    rw [hc]
    exact List.mem_map.mpr ⟨z, (FunctionalHardnessCompletion.Proof.completePatterns n).2 z, rfl⟩

private theorem mask_lookup {n : Nat} (z : Mask n) (i : Fin n) :
    (maskCode z).getD i.val false = z i := by
  simp [maskCode, List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt]

private theorem mod_tag (a tag : Nat) (h : tag < 6) : (6 * a + tag) % 6 = tag := by omega
private theorem div_tag (a tag : Nat) (h : tag < 6) : (6 * a + tag) / 6 = a := by omega

theorem exactRestriction : Targets.ExactRestriction := by
  intro n z d
  induction d with
  | unit => rw [expressionCode, restrictCode]; rfl
  | var i =>
      rw [expressionCode, restrictCode]
      simp only [mod_tag _ 1 (by decide), div_tag _ 1 (by decide), ↓reduceIte, mask_lookup]
      cases h : z i <;>
        simp [h, restrict, expressionCode, zeroExpression, SeededInputCode.zeroCode,
          SeededInputCode.variableCode, SeededInputCode.addCode, SeededInputCode.negateCode]
  | add a b iha ihb =>
      rw [expressionCode, restrictCode]
      simp [mod_tag _ 2 (by decide), div_tag _ 2 (by decide), Nat.unpair_pair,
        iha, ihb, restrict, expressionCode, SeededInputCode.addCode]
  | neg a ih =>
      rw [expressionCode, restrictCode]
      simp [mod_tag _ 3 (by decide), div_tag _ 3 (by decide),
        ih, restrict, expressionCode, SeededInputCode.negateCode]
  | shift a ih =>
      rw [expressionCode, restrictCode]
      simp [mod_tag _ 4 (by decide), div_tag _ 4 (by decide),
        ih, restrict, expressionCode, SeededInputCode.shiftCode]

theorem exactSystemRestriction : Targets.ExactSystemRestriction := by
  intro n z s
  simp only [restrictRows, restrictSystem, List.map_map]
  exact List.map_congr_left (fun _ _ => exactRestriction n z _)

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.MaskRestrictionCode.Proof
