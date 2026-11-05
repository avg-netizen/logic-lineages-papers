module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadIndexProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCodeProof
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCompilerTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationGraphProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureRowPrograms
open CommonHeadCode CommonHeadCode.Program CommonHeadCompiler CommonHeadLargeGuards IntegerAlgorithms.Proof
private abbrev Input := CommonHeadCode.Input
private abbrev Code := CommonHeadCode.Code
attribute [local irreducible] Nat.sqrt Nat.unpair branchKeys childConstant
  CommonHeadSmallFold.closedValueCode encodedCollapseValue encodedFiniteTail rawNormCode

private theorem computable_map {A B C:Type} [Primcodable A] [Primcodable B] [Primcodable C] [Inhabited B]
    {xs:A→List B} {f:A→B→C} (hx:Computable xs) (hf:Computable₂ f):
    Computable (fun a=>(xs a).map (f a)):=by
  have hs:Computable₂ (fun a:A=>fun p:B×List C=>f a p.1::p.2):=
    Primrec.list_cons.to_comp.comp (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  apply (BalancedBoxEvaluation.Graph.computable_foldr default hx (Computable.const []) hs).of_eq
  intro a
  induction xs a with
  | nil=>rfl
  | cons b bs ih=>simp only [List.foldr_cons,List.map_cons,ih]

private theorem head_program:Computable (fun a:Input=>a.2.1):=Computable.fst.comp Computable.snd
private theorem constant_program:Computable (fun a:Input=>a.2.2.1):=Computable.fst.comp (Computable.snd.comp Computable.snd)
private theorem coefficients_program:Computable (fun a:Input=>a.2.2.2.1):=
  Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
private theorem tail1_program:Computable (fun a:Input=>a.2):=Computable.snd
private theorem tail2_program:Computable (fun a:Input=>a.2.2):=
  (Computable.snd:Computable (fun q:Nat×(Int×List Int×Int)=>q.2)).comp tail1_program
private theorem tail3_program:Computable (fun a:Input=>a.2.2.2):=
  (Computable.snd:Computable (fun q:Int×(List Int×Int)=>q.2)).comp tail2_program
private theorem desired_program:Computable (fun a:Input=>a.2.2.2.2):=
  (Computable.snd:Computable (fun q:List Int×Int=>q.2)).comp tail3_program
private theorem keys_program:Computable (fun a:Input=>branchKeys a.2.1 a.2.2.1 a.2.2.2.1):=by
  have hp:Computable (fun a:Input=>(a.2.1,a.2.2.1,a.2.2.2.1)):=
    head_program.pair (constant_program.pair coefficients_program)
  exact branchKeys_primitive.to_comp.comp hp

private abbrev ChildContext:=(Input×Nat)×(Nat×Nat)
private theorem child_origin:Computable (fun p:ChildContext=>p.1.1):=Computable.fst.comp Computable.fst
private theorem child_fuel:Computable (fun p:ChildContext=>p.1.2):=Computable.snd.comp Computable.fst
private theorem child_index:Computable (fun p:ChildContext=>p.2.1):=Computable.fst.comp Computable.snd
private theorem child_numeral:Computable (fun p:ChildContext=>p.2.2):=Computable.snd.comp Computable.snd
private theorem child_head:Computable (fun p:ChildContext=>p.1.1.2.1):=head_program.comp child_origin
private theorem child_old_constant:Computable (fun p:ChildContext=>p.1.1.2.2.1):=constant_program.comp child_origin
private theorem child_coefficients:Computable (fun p:ChildContext=>p.1.1.2.2.2.1):=coefficients_program.comp child_origin
private theorem child_desired:Computable (fun p:ChildContext=>p.1.1.2.2.2.2):=desired_program.comp child_origin
private theorem closed_fold_parameters:Computable (fun p:ChildContext=>
    (p.1.1.2.1,p.1.1.2.2.1,p.1.1.2.2.2.1,p.2.1,p.2.2)):=
  child_head.pair (child_old_constant.pair (child_coefficients.pair (child_index.pair child_numeral)))
private theorem child_closed_value:Computable (fun p:ChildContext=>
    CommonHeadSmallFold.closedValueCode p.1.1.2.1 p.2.2):=
  CommonHeadSmallFold.Proof.closedEvaluation.1.comp child_head child_numeral
private theorem child_coefficient:Computable (fun p:ChildContext=>p.1.1.2.2.2.1.getD p.2.1 0):=
  (Primrec.list_getD (0:Int)).to_comp.comp child_coefficients child_index
private theorem child_closed_integer:Computable (fun p:ChildContext=>
    (CommonHeadSmallFold.closedValueCode p.1.1.2.1 p.2.2:Int)):=
  ofNat_primitive.to_comp.comp child_closed_value
private theorem child_product:Computable (fun p:ChildContext=>
    p.1.1.2.2.2.1.getD p.2.1 0*(CommonHeadSmallFold.closedValueCode p.1.1.2.1 p.2.2:Int)):=
  mul_primitive.to_comp.comp child_coefficient child_closed_integer
private theorem child_updated_constant:Computable (fun p:ChildContext=>
    childConstant p.1.1.2.1 p.1.1.2.2.1 p.1.1.2.2.2.1 p.2.1 p.2.2):=by
  apply (add_primitive.to_comp.comp child_old_constant child_product).of_eq
  intro p
  unfold childConstant
  rfl

private theorem child_remaining_coefficients:Computable (fun p:ChildContext=>p.1.1.2.2.2.1.eraseIdx p.2.1):=
  erase_primitive.to_comp.comp child_coefficients child_index
private theorem child_input_program:Computable₂ (fun p:Input×Nat=>fun key:Nat×Nat=>
    (p.2,p.1.2.1,childConstant p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 key.1 key.2,
      p.1.2.2.2.1.eraseIdx key.1,p.1.2.2.2.2)):=
  child_fuel.pair (child_head.pair (child_updated_constant.pair
    (child_remaining_coefficients.pair child_desired)))

private theorem positive_children_program:Computable₂ (fun a:Input=>fun n:Nat=>
    (branchKeys a.2.1 a.2.2.1 a.2.2.2.1).map (fun key=>
      (n,a.2.1,childConstant a.2.1 a.2.2.1 a.2.2.2.1 key.1 key.2,
        a.2.2.2.1.eraseIdx key.1,a.2.2.2.2))):=
  computable_map (keys_program.comp Computable.fst) child_input_program

theorem children_computable:Computable children:=by
  apply (Computable.nat_casesOn (Computable.fst:Computable (fun a:Input=>a.1))
    (Computable.const ([]:List Input)) positive_children_program).of_eq
  intro a
  unfold children
  cases h:a.1 <;> rfl

theorem assemble_computable:Computable₂ assemble:=by
  let T:=Input×List Code
  have hOrig:Computable (fun p:T=>p.1):=Computable.fst
  have hDesired:=desired_program.comp hOrig
  have hK:=constant_program.comp hOrig
  have hCS:=coefficients_program.comp hOrig
  have hbase:Computable (fun p:T=>constant (decide (Int.sign p.1.2.2.1=p.1.2.2.2.2))):=
    constant_primitive.to_comp.comp
      (Primrec.eq.decide.to_comp.comp (sign_primitive.to_comp.comp hK) hDesired)
  have hguard:Primrec₂ (fun key:Nat×Nat=>fun p:Code=>guardedCode key.1 key.2 p):=
    guarded_primitive.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  have hsmall:Computable (fun p:T=>disjoin (List.zipWith (fun key out=>guardedCode key.1 key.2 out)
      (branchKeys p.1.2.1 p.1.2.2.1 p.1.2.2.2.1) p.2)):=
    disjoin_primitive.to_comp.comp ((zipWith_primitive _ hguard).to_comp.comp
      (keys_program.comp hOrig) Computable.snd)
  have hlarge:Computable (fun p:T=>largeCode p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2):=
    large_primitive.to_comp.comp (hK.pair (hCS.pair hDesired))
  have hpositive:=disjunction_primitive.to_comp.comp hlarge hsmall
  apply (Computable.nat_casesOn (Computable.fst.comp Computable.fst) hbase
    (hpositive.comp Computable.fst).to₂).of_eq
  intro p
  unfold assemble
  cases h:p.1.1 <;> rfl

theorem codeInterfaces:CommonHeadCode.Targets.CodeInterfaces:=⟨children_computable,assemble_computable⟩

theorem allCodeEffectivity:CommonHeadCompiler.Targets.AllCodeEffectivity:=by
  have hrec:Computable recursiveCode:=
    (BalancedBoxEvaluation.Graph.exactDecreasingGraph Input Code children assemble (fun a=>a.1)
      children_computable assemble_computable Computable.fst recursiveCode
      CommonHeadCode.Proof.recursiveCodeEquation.1 CommonHeadCode.Proof.recursiveCodeEquation.2).2
  have hInput:Computable (fun p:Nat×Int×List Int×Int=>
      (p.2.2.1.length,p.1,p.2.1,p.2.2.1,p.2.2.2)):=
    (Primrec.list_length.to_comp.comp (Computable.fst.comp (Computable.snd.comp Computable.snd))).pair
      (Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
          (Computable.snd.comp (Computable.snd.comp Computable.snd)))))
  exact hrec.comp hInput
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureRowPrograms
