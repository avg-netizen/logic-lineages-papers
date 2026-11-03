module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsCodeTargets
public import LogicLineages.OrdinalComparison.RawComparisonProof
@[expose] public section

namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsCode.Proof
open CommonHeadLargeGuards (Formula)
open CommonHeadCompiler (encode)
open CommonHeadCode (constant conjunction disjunction negative conjoin disjoin)

private theorem head_code (heads : List NONote) (i : Nat) :
    headCode (encodeHeads heads) i = rawNoteEncode (heads.getD i 0).1 := by
  exact List.getD_map heads (0 : NONote) (fun h => rawNoteEncode h.1)

private theorem head_codes_equal (heads : List NONote) (i j : Nat) :
    headCode (encodeHeads heads) i = headCode (encodeHeads heads) j ↔
      heads.getD i 0 = heads.getD j 0 := by
  rw [head_code, head_code]
  constructor
  · intro h
    apply Subtype.ext
    have hd := congrArg rawNoteDecode h
    rw [rawNoteDecodeEncode (heads.getD i 0).1,
      rawNoteDecodeEncode (heads.getD j 0).1] at hd
    exact hd
  · intro h
    rw [h]

private theorem head_codes_compare (heads : List NONote) (i j : Nat) :
    rawComparisonCode (headCode (encodeHeads heads) i) (headCode (encodeHeads heads) j) =
      orderingCode (ONote.cmp (heads.getD i 0).1 (heads.getD j 0).1) := by
  rw [head_code, head_code]
  exact rawComparisonCorrect _ _

private theorem head_codes_less (heads : List NONote) (i j : Nat) :
    rawComparisonCode (headCode (encodeHeads heads) i) (headCode (encodeHeads heads) j) = 0 ↔
      (heads.getD i 0).1.repr < (heads.getD j 0).1.repr := by
  rw [head_code, head_code]
  exact (rawComparisonOrdinalCorrect (heads.getD i 0) (heads.getD j 0)).1

private theorem key_equal_code (heads : List NONote) (i j : Nat) :
    keyEqualCode (encodeHeads heads) i j =
      encode (BalancedLargeGuards.keyEqualFormula (fun k => heads.getD k 0) i j) := by
  classical
  by_cases h : heads.getD i 0 = heads.getD j 0
  · have hc := (head_codes_equal heads i j).mpr h
    simp only [keyEqualCode, BalancedLargeGuards.keyEqualFormula, if_pos hc, if_pos h]
    rfl
  · have hc : headCode (encodeHeads heads) i ≠ headCode (encodeHeads heads) j :=
      fun he => h ((head_codes_equal heads i j).mp he)
    simp only [keyEqualCode, BalancedLargeGuards.keyEqualFormula, if_neg hc, if_neg h]
    rfl

private theorem key_less_code (heads : List NONote) (i j : Nat) :
    keyLessCode (encodeHeads heads) i j =
      encode (BalancedLargeGuards.keyLessFormula (fun k => heads.getD k 0) i j) := by
  classical
  by_cases hl : (heads.getD i 0).1.repr < (heads.getD j 0).1.repr
  · have hc := (head_codes_less heads i j).mpr hl
    simp only [keyLessCode, BalancedLargeGuards.keyLessFormula, if_pos hc, if_pos hl]
    rfl
  · have hnc : rawComparisonCode (headCode (encodeHeads heads) i)
        (headCode (encodeHeads heads) j) ≠ 0 :=
      fun hc => hl ((head_codes_less heads i j).mp hc)
    simp only [keyLessCode, BalancedLargeGuards.keyLessFormula, if_neg hnc, if_neg hl]
    by_cases he : heads.getD i 0 = heads.getD j 0
    · have hc := (head_codes_equal heads i j).mpr he
      simp only [if_pos hc, if_pos he]
      rfl
    · have hc : headCode (encodeHeads heads) i ≠ headCode (encodeHeads heads) j :=
        fun h => he ((head_codes_equal heads i j).mp h)
      simp only [if_neg hc, if_neg he]
      rfl

theorem exactHeadsAndKeys : Targets.ExactHeadsAndKeys := by
  refine ⟨rfl, ?_⟩
  intro heads i j
  exact ⟨head_code heads i, head_codes_equal heads i j, head_codes_compare heads i j,
    head_codes_less heads i j, key_equal_code heads i j, key_less_code heads i j⟩

private theorem encode_conjoin (ps : List Formula) :
    encode (CommonHeadLargeGuards.conjunction ps) = conjoin (ps.map encode) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change encode p ++ encode (CommonHeadLargeGuards.conjunction ps) ++ [(6,0,0)] = _
    rw [ih]
    rfl

private theorem encode_disjoin (ps : List Formula) :
    encode (CommonHeadLargeGuards.disjunction ps) = disjoin (ps.map encode) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change encode p ++ encode (CommonHeadLargeGuards.disjunction ps) ++ [(7,0,0)] = _
    rw [ih]
    rfl

private theorem mask_code (heads : List NONote) (m i : Nat) (mask : List Bool) :
    maskCode (encodeHeads heads) m i mask =
      encode (BalancedLargeGuards.maskGuard (fun k => heads.getD k 0) m i mask) := by
  rw [BalancedLargeGuards.maskGuard, encode_conjoin]
  unfold maskCode
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro j hj
  by_cases hb : mask.getD j false = true
  · simpa only [Function.comp_apply, if_pos hb] using key_equal_code heads i j
  · simp only [Function.comp_apply, if_neg hb, encode, negative]
    rw [key_equal_code]

private theorem block_code (heads : List NONote) (cs : List Int) (i : Nat) (desired : Int) :
    blockCode (encodeHeads heads) cs i desired =
      encode (BalancedLargeGuards.blockFormula (fun k => heads.getD k 0) cs i desired) := by
  rw [BalancedLargeGuards.blockFormula, encode_disjoin]
  unfold blockCode
  congr 1
  simp only [List.map_map]
  exact List.map_congr_left (fun mask _ => mask_code heads cs.length i mask)

private theorem canceled_code (heads : List NONote) (cs : List Int) :
    canceledCode (encodeHeads heads) cs =
      encode (BalancedLargeGuards.canceledFormula (fun k => heads.getD k 0) cs) := by
  rw [BalancedLargeGuards.canceledFormula, encode_conjoin]
  unfold canceledCode
  congr 1
  simp only [List.map_map]
  exact List.map_congr_left (fun i _ => block_code heads cs i 0)

private theorem maximal_code (heads : List NONote) (cs : List Int) (i : Nat) :
    maximalCode (encodeHeads heads) cs i =
      encode (BalancedLargeGuards.maximalFormula (fun k => heads.getD k 0) cs i) := by
  rw [BalancedLargeGuards.maximalFormula, encode_conjoin]
  unfold maximalCode
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro j hj
  change disjunction (negative (keyLessCode (encodeHeads heads) i j))
    (blockCode (encodeHeads heads) cs j 0) = _
  rw [key_less_code, block_code]
  rfl

theorem exactFiniteGuardCode : Targets.ExactFiniteGuardCode := by
  intro heads
  exact ⟨mask_code heads, block_code heads, canceled_code heads, maximal_code heads⟩

private theorem difference_sign_code (left right : Nat) (desired : Int) :
    differenceSignCode left right desired =
      encode (BalancedLargeGuards.differenceSignFormula left right desired) := by
  unfold differenceSignCode BalancedLargeGuards.differenceSignFormula
  split_ifs <;> rfl

private theorem sign_code (heads : List NONote) (cs : List Int) (desired : Int) :
    signCode (encodeHeads heads) cs desired =
      encode (BalancedLargeGuards.signFormula (fun k => heads.getD k 0) cs desired) := by
  have hleft : conjunction (canceledCode (encodeHeads heads) cs)
      (differenceSignCode cs.length (cs.length + 1) desired) =
      encode (.conj (BalancedLargeGuards.canceledFormula (fun k => heads.getD k 0) cs)
        (BalancedLargeGuards.differenceSignFormula cs.length (cs.length + 1) desired)) := by
    rw [canceled_code, difference_sign_code]
    rfl
  have hright : (if desired = 0 then constant false else
      disjoin ((List.range cs.length).map (fun i =>
        conjunction (blockCode (encodeHeads heads) cs i desired)
          (maximalCode (encodeHeads heads) cs i)))) =
      encode (if desired = 0 then .falsity else CommonHeadLargeGuards.disjunction
        ((List.range cs.length).map (fun i =>
          .conj (BalancedLargeGuards.blockFormula (fun k => heads.getD k 0) cs i desired)
            (BalancedLargeGuards.maximalFormula (fun k => heads.getD k 0) cs i)))) := by
    by_cases hd : desired = 0
    · simp [hd, constant, encode]
    · simp only [if_neg hd, encode_disjoin, List.map_map]
      apply congrArg disjoin
      apply List.map_congr_left
      intro i hi
      rw [block_code, maximal_code]
      rfl
  unfold signCode BalancedLargeGuards.signFormula
  rw [hleft, hright]
  rfl

private theorem large_code (L : Nat) (heads : List NONote) (cs : List Int) (desired : Int) :
    largeCode L (encodeHeads heads) cs desired =
      encode (BalancedLargeGuards.largeFormula L (fun k => heads.getD k 0) cs desired) := by
  rw [BalancedLargeGuards.largeFormula]
  change conjunction _ (signCode (encodeHeads heads) cs desired) = _
  rw [sign_code]
  unfold conjunction
  congr 2
  rw [encode_conjoin]
  simp only [List.map_map, Function.comp_def, encode]

theorem exactLargeGuardCode : Targets.ExactLargeGuardCode := by
  exact ⟨difference_sign_code, sign_code, large_code⟩

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsCode.Proof
