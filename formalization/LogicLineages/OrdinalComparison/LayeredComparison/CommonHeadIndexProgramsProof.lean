module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadGuardProgramsProof
public import LogicLineages.OrdinalComparison.RawNormCode
public import LogicLineages.OrdinalComparison.CommonHeadSmallFoldEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCode.Program
open CommonHeadCompiler IntegerAlgorithms.Proof

theorem skip_primitive:Primrec₂ CommonHeadGuardReindex.skip:=
  Primrec.ite (Primrec.nat_lt.comp Primrec.snd Primrec.fst) Primrec.snd (Primrec.succ.comp Primrec.snd)

theorem rename_primitive:Primrec₂ (fun i:Nat=>fun a:Instruction=>
    renameInstruction (CommonHeadGuardReindex.skip i) a):=by
  let D:=Nat×Instruction
  have ht:Primrec (fun p:D=>p.2.1):=Primrec.fst.comp Primrec.snd
  have hx:Primrec (fun p:D=>p.2.2.1):=Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hy:Primrec (fun p:D=>p.2.2.2):=Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hsx:=skip_primitive.comp (Primrec.fst:Primrec (fun p:D=>p.1)) hx
  have hsy:=skip_primitive.comp (Primrec.fst:Primrec (fun p:D=>p.1)) hy
  have h23:PrimrecPred (fun p:D=>p.2.1=2∨p.2.1=3):=
    (Primrec.eq.comp ht (Primrec.const 2)).or (Primrec.eq.comp ht (Primrec.const 3))
  exact Primrec.ite h23 (ht.pair (hsx.pair hsy))
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 4)) ((Primrec.const 4).pair (hx.pair hsy)) Primrec.snd)

theorem skipCode_primitive:Primrec₂ skipCode:=
  Primrec.list_map Primrec.snd
    (rename_primitive.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

theorem guarded_primitive:Primrec (fun p:Nat×Nat×Code=>guardedCode p.1 p.2.1 p.2.2):=by
  let D:=Nat×Nat×Code
  have hi:Primrec (fun p:D=>p.1):=Primrec.fst
  have hc:Primrec (fun p:D=>p.2.1):=Primrec.fst.comp Primrec.snd
  have hp:Primrec (fun p:D=>p.2.2):=Primrec.snd.comp Primrec.snd
  have hlo:Primrec (fun p:D=>[(4,p.2.1,p.1)]):=
    Primrec.list_cons.comp ((Primrec.const 4).pair (hc.pair hi)) (Primrec.const [])
  have hup:Primrec (fun p:D=>[(4,p.2.1+1,p.1)]):=
    Primrec.list_cons.comp ((Primrec.const 4).pair ((Primrec.succ.comp hc).pair hi)) (Primrec.const [])
  exact conjunction_primitive.comp (conjunction_primitive.comp hlo (negative_primitive.comp hup))
    (skipCode_primitive.comp hi hp)

theorem erase_primitive:Primrec₂ (fun cs:List Int=>fun i:Nat=>cs.eraseIdx i):=by
  have ht:Primrec (fun p:List Int×Nat=>p.1.take p.2):=
    Primrec.list_take.comp Primrec.snd Primrec.fst
  have hd:Primrec (fun p:List Int×Nat=>p.1.drop (p.2+1)):=
    Primrec.list_drop.comp (Primrec.succ.comp Primrec.snd) Primrec.fst
  apply (Primrec.list_append.comp ht hd).of_eq
  intro p
  rcases p with ⟨cs,i⟩
  induction cs generalizing i with
  | nil=>simp
  | cons x cs ih=>
    cases i with
    | zero=>rfl
    | succ i=>simp [List.eraseIdx,ih]

theorem smallNumerals_primitive:Primrec (fun p:Nat×Int×List Int=>smallNumerals p.1 p.2.1 p.2.2):=by
  let D:=Nat×Int×List Int
  have hh:Primrec (fun p:D=>p.1):=Primrec.fst
  have hk:Primrec (fun p:D=>p.2.1):=Primrec.fst.comp Primrec.snd
  have hcs:Primrec (fun p:D=>p.2.2):=Primrec.snd.comp Primrec.snd
  have hnorm:Primrec rawNormCode:=Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have hpred:PrimrecRel (fun c h:Nat=>rawNormCode h≤c):=
    Primrec.nat_le.comp (hnorm.comp Primrec.snd) Primrec.fst
  exact hpred.listFilter.comp (Primrec.list_range.comp (threshold_primitive.comp hk hcs)) hh

theorem branchKeys_primitive:Primrec (fun p:Nat×Int×List Int=>branchKeys p.1 p.2.1 p.2.2):=by
  let D:=Nat×Int×List Int
  have hsmall:Primrec (fun p:D=>smallNumerals p.1 p.2.1 p.2.2):=smallNumerals_primitive
  have heach:Primrec₂ (fun p:D=>fun i:Nat=>(smallNumerals p.1 p.2.1 p.2.2).map (fun c=>(i,c))):=
    Primrec.list_map (hsmall.comp Primrec.fst)
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂
  exact Primrec.list_flatMap
    (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))) heach

theorem childConstant_computable:Computable (fun p:Nat×Int×List Int×Nat×Nat=>
    childConstant p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2):=by
  let D:=Nat×Int×List Int×Nat×Nat
  have hh:Computable (fun p:D=>p.1):=Computable.fst
  have hk:Computable (fun p:D=>p.2.1):=Computable.fst.comp Computable.snd
  have hcs:Computable (fun p:D=>p.2.2.1):=Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hi:Computable (fun p:D=>p.2.2.2.1):=Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hc:Computable (fun p:D=>p.2.2.2.2):=Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hv:=CommonHeadSmallFold.Proof.closedEvaluation.1.comp hh hc
  exact add_primitive.to_comp.comp hk (mul_primitive.to_comp.comp
    ((Primrec.list_getD (0:Int)).to_comp.comp hcs hi) (ofNat_primitive.to_comp.comp hv))
end LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCode.Program
