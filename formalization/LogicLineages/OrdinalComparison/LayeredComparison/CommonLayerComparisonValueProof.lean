module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparisonTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerSyntaxProof
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCompilerProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparison.Proof
open CommonLayerSyntax CommonHeadLargeGuards CommonHeadLargeRow

theorem sign_zero (a b:Nat):Int.sign ((a:Int)-(b:Int))=0↔a=b:=by
  rw [Int.sign_eq_zero_iff_zero]
  omega
theorem sign_negative (a b:Nat):Int.sign ((a:Int)-(b:Int))= -1↔a<b:=by
  rw [Int.sign_eq_neg_one_iff_neg]
  omega
theorem sign_positive (a b:Nat):Int.sign ((a:Int)-(b:Int))=1↔b<a:=by
  rw [Int.sign_eq_one_iff_pos]
  omega

theorem base_exact (E F:Nat) (desired:Int) (ν:Nat→Nat):
    (baseCompare E F desired).eval ν↔
      Int.sign (((BaseTerm.decode E).value ν:Int)-((BaseTerm.decode F).value ν:Int))=desired:=by
  by_cases h0:desired=0
  · subst desired
    simp only [baseCompare,if_pos rfl,BaseFormula.Formula.eval]
    exact (sign_zero _ _).symm
  by_cases hn:desired= -1
  · subst desired
    simp only [baseCompare,if_neg (by decide :(-1:Int)≠0),if_pos rfl,BaseFormula.Formula.eval]
    exact (sign_negative _ _).symm
  by_cases hp:desired=1
  · subst desired
    simp only [baseCompare,if_neg (by decide :(1:Int)≠0),if_neg (by decide :(1:Int)≠ -1),if_pos rfl,
      BaseFormula.Formula.eval]
    exact (sign_positive _ _).symm
  simp only [baseCompare,if_neg h0,if_neg hn,if_neg hp,BaseFormula.Formula.eval,false_iff]
  intro hs
  rcases lt_trichotomy ((BaseTerm.decode E).value ν) ((BaseTerm.decode F).value ν) with hl|he|hr
  · have h:= (sign_negative _ _).2 hl
    exact hn (hs.symm.trans h)
  · have h:= (sign_zero _ _).2 he
    exact h0 (hs.symm.trans h)
  · have h:= (sign_positive _ _).2 hr
    exact hp (hs.symm.trans h)

theorem constant_value (Γ:List Nat) (c:Nat) (ν:Nat→Nat):
    codedValue Γ (constantCode Γ.length c) ν=c:=by
  cases Γ with
  | nil=>
    change (BaseTerm.decode (BaseTerm.encode (.numeral c))).value ν=c
    rw [CommonLayerSyntax.Proof.baseRoundtrip (.numeral c)]
    rfl
  | cons h Γ=>
    simp [constantCode,codedValue,payload]

theorem constant_variables (n c:Nat):codedVariables n (constantCode n c)=[]:=by
  cases n with
  | zero=>
    change (BaseTerm.decode (BaseTerm.encode (.numeral c))).variables=[]
    rw [CommonLayerSyntax.Proof.baseRoundtrip (.numeral c)]
    rfl
  | succ n=>simp [codedVariables,constantCode,decodeCommon,commonVariables,payload]

private theorem input_row_exact (atoms:List (Int×Nat)) (f:Nat→Nat) (N d:Nat):
    inputRow (atoms.map Prod.fst) (fun i=>N+f ((atoms.map Prod.snd).getD i d))=
      atoms.map (fun a=>(a.1,N+f a.2)):=by
  apply List.ext_getElem
  · simp [inputRow]
  · intro i hi hj
    simp only [inputRow,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]
    rw [List.getD_eq_getElem _ d (by simpa using hj)]
    simp only [List.getElem_map]

private theorem coded_cast (h:Nat) (Γ:List Nat) (code:Nat) (ν:Nat→Nat):
    (codedValue (h::Γ) code ν:Int)=(payload code).1+
      ((payload code).2.map (fun a=>(a.1+1:Int)*
        (CommonHeadSmallFold.closedValueCode h (rawNormCode h+codedValue Γ a.2 ν):Int))).sum:=by
  simp [codedValue,Nat.cast_sum,Nat.cast_add,Nat.cast_mul,List.map_map,Function.comp_def]

private theorem map_sum_negative {α:Type} (xs:List α) (f:α→Int):
    (xs.map (fun a=> -(f a))).sum= -(xs.map f).sum:=by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>simp only [List.map_cons,List.sum_cons,ih,neg_add]

theorem row_difference (rho:NONote) (Γ:List Nat) (E F:Nat) (ν:Nat→Nat):
    value rho.1.repr (rowConstant E F)
      (inputRow (rowCoefficients E F) (fun i=>rawNormCode (rawNoteEncode rho.1)+
        codedValue Γ ((rowArguments E F).getD i (constantCode Γ.length 0)) ν))=
    (codedValue (rawNoteEncode rho.1::Γ) E ν:Int)-
      (codedValue (rawNoteEncode rho.1::Γ) F ν:Int):=by
  unfold rowCoefficients rowArguments
  rw [input_row_exact (signedAtoms E F) (fun t=>codedValue Γ t ν)
    (rawNormCode (rawNoteEncode rho.1)) (constantCode Γ.length 0)]
  unfold value rowConstant signedAtoms
  simp only [List.map_append,List.map_map,List.sum_append]
  have head (t:Nat):actualHeadValue rho.1.repr t=
      CommonHeadSmallFold.closedValueCode (rawNoteEncode rho.1) t:=
    ((CommonHeadSmallFold.Proof.closedEvaluation.2 rho t).1).symm
  simp only [Function.comp_def,head,neg_mul]
  rw [map_sum_negative]
  rw [coded_cast,coded_cast]
  ring
end LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparison.Proof
