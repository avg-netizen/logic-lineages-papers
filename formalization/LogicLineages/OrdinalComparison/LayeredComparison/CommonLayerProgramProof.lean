module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerProgramTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerProgram.Proof
open CommonLayerComparison CommonLayerSyntax CommonHeadCompiler

/-- This base syntax is a genuine bijective numeric codec, not a supplied
interpreter. Every raw natural code has an actual literal BASE term. -/
theorem base_code_roundtrip (n:Nat):BaseTerm.encode (BaseTerm.decode n)=n:=by
  induction n using Nat.strong_induction_on with
  | h n ih=>
    rw [BaseTerm.decode]
    split_ifs with h0 h1 h2
    · change 4*(n/4)=n
      omega
    · change 4*(n/4)+1=n
      omega
    · have hn:0<n:=by omega
      have hd:n/4<n:=Nat.div_lt_self hn (by decide)
      have hl:(n/4).unpair.1<n:=lt_of_le_of_lt (Nat.unpair_left_le _) hd
      have hr:(n/4).unpair.2<n:=lt_of_le_of_lt (Nat.unpair_right_le _) hd
      change 4*Nat.pair (BaseTerm.encode (BaseTerm.decode (n/4).unpair.1))
        (BaseTerm.encode (BaseTerm.decode (n/4).unpair.2))+2=n
      rw [ih _ hl,ih _ hr,Nat.pair_unpair]
      omega
    · have hn:0<n:=by omega
      have hd:n/4<n:=Nat.div_lt_self hn (by decide)
      change 4*BaseTerm.encode (BaseTerm.decode (n/4))+3=n
      rw [ih _ hd]
      omega

private theorem base_code (E F:Nat) (desired:Int):
    (baseCompare E F desired).encode=baseCode E F desired:=by
  unfold baseCompare baseCode
  split_ifs <;>simp only [BaseFormula.Formula.encode,BaseFormula.Formula.guardView,
    CommonHeadCompiler.encode,base_code_roundtrip]

private theorem child_heads (Γ:List Nat) (N:Nat) (args:List Nat) (q:Instruction):
    (child Γ N args q).1=Γ:=by
  unfold child
  split_ifs <;>rfl

private theorem base_negative (p:BaseFormula.Formula):
    (BaseFormula.Formula.negative p).encode=p.encode++[(5,0,0)]:=rfl
private theorem base_conjunction (p q:BaseFormula.Formula):
    (BaseFormula.Formula.conjunction p q).encode=p.encode++q.encode++[(6,0,0)]:=rfl
private theorem base_disjunction (p q:BaseFormula.Formula):
    (BaseFormula.Formula.disjunction p q).encode=p.encode++q.encode++[(7,0,0)]:=rfl

private theorem translate_encode (Γ:List Nat) (N:Nat) (args:List Nat)
    (p:CommonHeadLargeGuards.Formula):
    (translateGuard (CommonLayerComparison.compile Γ) Γ.length N args p).encode=
      (CommonHeadCompiler.encode p).flatMap (fun q=>
        instructionCode N q (recursiveCode (child Γ N args q))):=by
  induction p with
  | truth=>simp [translateGuard,BaseFormula.Formula.encode,BaseFormula.Formula.guardView,
      CommonHeadCompiler.encode,instructionCode]
  | falsity=>simp [translateGuard,BaseFormula.Formula.encode,BaseFormula.Formula.guardView,
      CommonHeadCompiler.encode,instructionCode]
  | eq i j=>simp [translateGuard,CommonHeadCompiler.encode,instructionCode,child,
      recursiveCode,CommonLayerComparison.compileCode]
  | lt i j=>simp [translateGuard,CommonHeadCompiler.encode,instructionCode,child,
      recursiveCode,CommonLayerComparison.compileCode]
  | bound c i=>
    by_cases hc:c≤N
    · simp [translateGuard,hc,BaseFormula.Formula.encode,BaseFormula.Formula.guardView,
        CommonHeadCompiler.encode,instructionCode]
    · simp [translateGuard,hc,BaseFormula.Formula.encode,BaseFormula.Formula.guardView,
        CommonHeadCompiler.encode,instructionCode,child,recursiveCode,CommonLayerComparison.compileCode]
  | neg p ih=>
    rw [translateGuard,base_negative,ih]
    simp only [CommonHeadCompiler.encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil]
    rfl
  | conj p q ihp ihq=>
    rw [translateGuard,base_conjunction,ihp,ihq]
    simp only [CommonHeadCompiler.encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil]
    rfl
  | disj p q ihp ihq=>
    rw [translateGuard,base_disjunction,ihp,ihq]
    simp only [CommonHeadCompiler.encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil]
    rfl

private theorem zip_assembly {α β γ:Type} (xs:List α) (f:α→β) (g:α→β→List γ):
    (xs.zipWith g (xs.map f)).flatten=xs.flatMap (fun x=>g x (f x)):=by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simp only [List.map_cons,List.zipWith_cons_cons,List.flatten_cons,List.flatMap_cons,ih]

theorem finiteCallEquation:Targets.ExactFiniteCallEquation:=by
  constructor
  · intro a b hb
    rcases a with ⟨Γ,E,F,d⟩
    cases Γ with
    | nil=>simp [children] at hb
    | cons h Γ=>
      obtain ⟨q,hq,hb⟩:=List.mem_map.mp hb
      subst b
      simp only [measure,child_heads,List.length_cons]
      omega
  · intro a
    rcases a with ⟨Γ,E,F,d⟩
    cases Γ with
    | nil=>exact base_code E F d
    | cons h Γ=>
      simp only [recursiveCode,CommonLayerComparison.compileCode,CommonLayerComparison.compile,
        children,assemble,List.map_map]
      rw [zip_assembly]
      exact translate_encode Γ (rawNormCode h) (rowArguments E F) _
end LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerProgram.Proof
