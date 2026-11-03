module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluationDataProgramsProof
public import LogicLineages.OrdinalComparison.CommonHeadSmallFoldEvaluationProof
public import LogicLineages.OrdinalComparison.ComparisonAssemblyListProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluation.Program
attribute [local irreducible] Nat.sqrt Nat.unpair rawNormCode atomInput CommonHeadSmallFold.closedValueCode

theorem atom_data:Primrec (fun p:AtomContext=>p.2):=Primrec.snd
theorem atom_size:Primrec (fun p:AtomContext=>p.1.1):=ctx_size.comp Primrec.fst
theorem atom_results:Primrec (fun p:AtomContext=>p.1.2.2):=ctx_results.comp Primrec.fst
theorem atom_weight:Primrec (fun p:AtomContext=>p.2.1+1):=Primrec.succ.comp (Primrec.fst.comp atom_data)
theorem atom_tail:Primrec (fun p:AtomContext=>p.2.2):=Primrec.snd.comp atom_data
theorem atom_head:Primrec (fun p:AtomContext=>p.2.2.1):=Primrec.fst.comp atom_tail
theorem atom_offset_tail:Primrec (fun p:AtomContext=>p.2.2.2):=Primrec.snd.comp atom_tail
theorem atom_offset:Primrec (fun p:AtomContext=>p.2.2.2.1):=Primrec.fst.comp atom_offset_tail
theorem atom_factors:Primrec (fun p:AtomContext=>p.2.2.2.2):=Primrec.snd.comp atom_offset_tail

theorem atom_index_factor:Primrec (fun p:AtomIndexContext=>p.1.2.2.2.2.getD p.2 0+1):=
  Primrec.succ.comp ((Primrec.list_getD (0:Nat)).comp (atom_factors.comp Primrec.fst) Primrec.snd)
theorem atom_index_result:Primrec (fun p:AtomIndexContext=>p.1.1.2.2.getD p.2 (0,[])):=
  (Primrec.list_getD ((0,[]):Result)).comp (atom_results.comp Primrec.fst) Primrec.snd
theorem atom_index_value:Primrec (fun p:AtomIndexContext=>(p.1.1.2.2.getD p.2 (0,[])).1):=
  Primrec.fst.comp atom_index_result

theorem atom_sum:Primrec (fun p:AtomContext=>((List.range p.1.1).map
    (fun j=>(p.2.2.2.2.getD j 0+1)*(p.1.2.2.getD j (0,[])).1)).sum):=
  CommonHeadCode.Program.sum_nat_primitive.comp (Primrec.list_map
    (Primrec.list_range.comp atom_size) (Primrec.nat_mul.comp atom_index_factor atom_index_value).to₂)

theorem raw_norm_primitive:Primrec rawNormCode:=Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive

theorem atom_input:Primrec (fun p:AtomContext=>atomInput p.1.1 p.2
    (fun j=>(p.1.2.2.getD j (0,[])).1)):=by
  apply (Primrec.nat_add.comp (Primrec.nat_add.comp (raw_norm_primitive.comp atom_head) atom_offset) atom_sum).of_eq
  intro p
  unfold atomInput
  rfl

theorem atom_value_computable:Computable (fun p:AtomContext=>(p.2.1+1)*
    CommonHeadSmallFold.closedValueCode p.2.2.1 (atomInput p.1.1 p.2 (fun j=>(p.1.2.2.getD j (0,[])).1))):=
  Primrec.nat_mul.to_comp.comp atom_weight.to_comp
    (CommonHeadSmallFold.Proof.closedEvaluation.1.comp atom_head.to_comp atom_input.to_comp)

private theorem computable_map {A B D:Type} [Primcodable A] [Primcodable B] [Primcodable D] [Inhabited B]
    {xs:A→List B} {f:A→B→D} (hx:Computable xs) (hf:Computable₂ f):
    Computable (fun a=>(xs a).map (f a)):=by
  have hs:Computable₂ (fun a:A=>fun p:B×List D=>f a p.1::p.2):=
    Primrec.list_cons.to_comp.comp (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  apply (ComparisonAssembly.computable_foldr default hx (Computable.const []) hs).of_eq
  intro a
  induction xs a with
  | nil=>rfl
  | cons b bs ih=>simp only [List.foldr_cons,List.map_cons,ih]

theorem heads_sum_computable:Computable (fun p:EvalContext=>
    (p.2.1.2.2.map (fun a=>(a.1+1)*CommonHeadSmallFold.closedValueCode a.2.1
      (atomInput p.1 a (fun j=>(p.2.2.getD j (0,[])).1)))).sum):=
  CommonHeadCode.Program.sum_nat_primitive.to_comp.comp
    (computable_map ctx_atoms.to_comp atom_value_computable)

theorem value_computable:Computable (fun p:EvalContext=>valueAt p.1 p.2.1
    (fun j=>(p.2.2.getD j (0,[])).1)):=
  Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp ctx_constant.to_comp outside_sum.to_comp)
    heads_sum_computable
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluation.Program
