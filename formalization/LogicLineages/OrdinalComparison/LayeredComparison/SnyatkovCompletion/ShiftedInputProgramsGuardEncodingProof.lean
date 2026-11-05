module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputProgramsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputProgramsProof.GuardEncoding
open CommonHeadLargeGuards CommonHeadCompiler CommonHeadCode

private theorem encode_conjoin (ps:List Formula):
    encode (CommonHeadLargeGuards.conjunction ps)=conjoin (ps.map encode):=by
  induction ps with
  | nil=>rfl
  | cons p ps ih=>
    change encode p++encode (CommonHeadLargeGuards.conjunction ps)++[(6,0,0)]=_
    rw [ih]
    rfl
private theorem encode_disjoin (ps:List Formula):
    encode (CommonHeadLargeGuards.disjunction ps)=disjoin (ps.map encode):=by
  induction ps with
  | nil=>rfl
  | cons p ps ih=>
    change encode p++encode (CommonHeadLargeGuards.disjunction ps)++[(7,0,0)]=_
    rw [ih]
    rfl
private theorem mask_code (m i:Nat) (mask:List Bool):
    maskCode m i mask=encode (maskGuard m i mask):=by
  rw [maskGuard,encode_conjoin]
  unfold maskCode
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro j hj
  by_cases hb:mask.getD j false=true
  · simp only [Function.comp_apply,if_pos hb,encode]
  · simp only [Function.comp_apply,if_neg hb,encode,negative]
theorem block_code (cs:List Int) (i:Nat) (desired:Int):
    blockCode cs i desired=encode (blockFormula cs i desired):=by
  rw [blockFormula,encode_disjoin]
  unfold blockCode
  congr 1
  simp only [List.map_map]
  exact List.map_congr_left (fun mask _=>mask_code cs.length i mask)
theorem canceled_code (cs:List Int):canceledCode cs=encode (canceledFormula cs):=by
  rw [canceledFormula,encode_conjoin]
  unfold canceledCode
  congr 1
  simp only [List.map_map]
  exact List.map_congr_left (fun i _=>block_code cs i 0)
private theorem maximal_code (cs:List Int) (i:Nat):maximalCode cs i=encode (maximalFormula cs i):=by
  rw [maximalFormula,encode_conjoin]
  unfold maximalCode
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro j hj
  change disjunction (negative [(3,i,j)]) (blockCode cs j 0)=_
  rw [block_code]
  rfl
theorem sign_code (K:Int) (cs:List Int) (desired:Int):
    signCode K cs desired=encode (signFormula K cs desired):=by
  have hleft:conjunction (constant (decide (Int.sign K=desired))) (canceledCode cs)=
      encode (.conj (if Int.sign K=desired then .truth else .falsity) (canceledFormula cs)):=by
    rw [canceled_code]
    by_cases hs:Int.sign K=desired <;> simp [hs,constant,CommonHeadCode.conjunction,encode]
  have hright:(if desired=0 then constant false else disjoin ((List.range cs.length).map (fun i=>
      conjunction (blockCode cs i desired) (maximalCode cs i))))=
      encode (if desired=0 then .falsity else CommonHeadLargeGuards.disjunction
        ((List.range cs.length).map (fun i=>.conj (blockFormula cs i desired) (maximalFormula cs i)))):=by
    by_cases hd:desired=0
    · simp [hd,constant,encode]
    · simp only [if_neg hd,encode_disjoin,List.map_map]
      apply congrArg disjoin
      apply List.map_congr_left
      intro i hi
      rw [block_code,maximal_code]
      rfl
  unfold signCode signFormula
  rw [hleft,hright]
  rfl


end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputProgramsProof.GuardEncoding
