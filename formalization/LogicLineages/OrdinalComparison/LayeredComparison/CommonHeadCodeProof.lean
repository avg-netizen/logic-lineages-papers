module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCodeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCode.Proof
open CommonHeadLargeGuards CommonHeadCompiler

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
private theorem block_code (cs:List Int) (i:Nat) (desired:Int):
    blockCode cs i desired=encode (blockFormula cs i desired):=by
  rw [blockFormula,encode_disjoin]
  unfold blockCode
  congr 1
  simp only [List.map_map]
  exact List.map_congr_left (fun mask _=>mask_code cs.length i mask)
private theorem canceled_code (cs:List Int):canceledCode cs=encode (canceledFormula cs):=by
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
private theorem sign_code (K:Int) (cs:List Int) (desired:Int):
    signCode K cs desired=encode (signFormula K cs desired):=by
  have hleft:conjunction (constant (decide (Int.sign K=desired))) (canceledCode cs)=
      encode (.conj (if Int.sign K=desired then .truth else .falsity) (canceledFormula cs)):=by
    rw [canceled_code]
    by_cases hs:Int.sign K=desired <;> simp [hs,constant,conjunction,encode]
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

theorem largeCodeExact : Targets.LargeCodeExact:=by
  intro K cs desired
  rw [largeFormula]
  change conjunction _ (signCode K cs desired)=_
  rw [sign_code]
  unfold conjunction
  congr 2
  rw [encode_conjoin]
  simp only [List.map_map,Function.comp_def,encode]

private theorem encode_rename (σ:Nat→Nat) (p:Formula):
    encode (CommonHeadGuardReindex.rename σ p)=(encode p).map (renameInstruction σ):=by
  induction p with
  | truth=>rfl
  | falsity=>rfl
  | eq i j=>simp [CommonHeadGuardReindex.rename,encode,renameInstruction]
  | lt i j=>simp [CommonHeadGuardReindex.rename,encode,renameInstruction]
  | bound c i=>simp [CommonHeadGuardReindex.rename,encode,renameInstruction]
  | neg p ih=>simp only [CommonHeadGuardReindex.rename,encode,List.map_append,ih];rfl
  | conj p q ihp ihq=>simp only [CommonHeadGuardReindex.rename,encode,List.map_append,ihp,ihq];rfl
  | disj p q ihp ihq=>simp only [CommonHeadGuardReindex.rename,encode,List.map_append,ihp,ihq];rfl

theorem guardCodeExact : Targets.GuardCodeExact:=by
  intro i c p
  simp only [guardedCode,CommonHeadGuardReindex.guarded,CommonHeadGuardReindex.equalConstant,encode]
  rw [encode_rename]
  rfl

private theorem zip_map {A B C:Type} (xs:List A) (f:A→B) (g:A→B→C):
    List.zipWith g xs (xs.map f)=xs.map (fun a=>g a (f a)):=by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>simp only [List.map_cons,List.zipWith_cons_cons,ih]

theorem recursiveCodeEquation : Targets.RecursiveCodeEquation:=by
  constructor
  · intro a b hb
    cases h:a.1 with
    | zero=>simp [children,h] at hb
    | succ n=>
      simp only [children,h] at hb
      obtain ⟨key,hkey,rfl⟩:=List.mem_map.mp hb
      simp [h]
  · intro a
    rcases a with ⟨fuel,h,K,cs,desired⟩
    cases fuel with
    | zero=>
      by_cases hs:Int.sign K=desired <;> simp [recursiveCode,compileFuel,assemble,constant,hs,encode]
    | succ n=>
      simp only [recursiveCode,compileFuel,encode,assemble,children,List.map_map,Function.comp_def]
      rw [zip_map]
      unfold disjunction
      rw [largeCodeExact]
      congr 2
      rw [encode_disjoin]
      unfold branchKeys
      simp only [List.map_flatMap,List.map_map,Function.comp_def]
      apply congrArg disjoin
      apply congrArg List.flatten
      apply List.map_congr_left
      intro i hi
      apply List.map_congr_left
      intro c hc
      exact (guardCodeExact i c _).symm
end LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCode.Proof
