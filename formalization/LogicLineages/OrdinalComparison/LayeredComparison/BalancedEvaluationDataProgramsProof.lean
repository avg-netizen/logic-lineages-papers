module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluationTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadIndexProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluation.Program
attribute [local irreducible] Nat.sqrt Nat.unpair rawNormCode
abbrev EvalContext:=Nat×UpperData×List Result
abbrev IndexContext:=EvalContext×Nat
abbrev AtomContext:=EvalContext×AtomData
abbrev AtomIndexContext:=AtomContext×Nat

theorem upperData_primitive:Primrec upperData:=
  Primrec.option_getD.comp (Primrec.decode:Primrec (fun n:Nat=>(Encodable.decode n:Option UpperData)))
    (Primrec.const (0,[],[]))
theorem certificateData_primitive:Primrec certificateData:=
  Primrec.option_getD.comp (Primrec.decode:Primrec (fun n:Nat=>(Encodable.decode n:Option CertificateData)))
    (Primrec.const (0,[]))

theorem ctx_size:Primrec (fun p:EvalContext=>p.1):=Primrec.fst
theorem ctx_upper:Primrec (fun p:EvalContext=>p.2.1):=Primrec.fst.comp Primrec.snd
theorem ctx_results:Primrec (fun p:EvalContext=>p.2.2):=Primrec.snd.comp Primrec.snd
theorem ctx_constant:Primrec (fun p:EvalContext=>p.2.1.1):=Primrec.fst.comp ctx_upper
theorem ctx_upper_tail:Primrec (fun p:EvalContext=>p.2.1.2):=Primrec.snd.comp ctx_upper
theorem ctx_outside:Primrec (fun p:EvalContext=>p.2.1.2.1):=Primrec.fst.comp ctx_upper_tail
theorem ctx_atoms:Primrec (fun p:EvalContext=>p.2.1.2.2):=Primrec.snd.comp ctx_upper_tail
theorem ctx_range:Primrec (fun p:EvalContext=>List.range p.1):=Primrec.list_range.comp ctx_size

theorem index_coefficient:Primrec (fun p:IndexContext=>p.1.2.1.2.1.getD p.2 0):=
  (Primrec.list_getD (0:Nat)).comp (ctx_outside.comp Primrec.fst) Primrec.snd
theorem index_result:Primrec (fun p:IndexContext=>p.1.2.2.getD p.2 (0,[])):=
  (Primrec.list_getD ((0,[]):Result)).comp (ctx_results.comp Primrec.fst) Primrec.snd
theorem index_value:Primrec (fun p:IndexContext=>(p.1.2.2.getD p.2 (0,[])).1):=Primrec.fst.comp index_result
theorem index_variables:Primrec (fun p:IndexContext=>(p.1.2.2.getD p.2 (0,[])).2):=Primrec.snd.comp index_result

theorem outside_sum:Primrec (fun p:EvalContext=>
    ((List.range p.1).map (fun j=>p.2.1.2.1.getD j 0*(p.2.2.getD j (0,[])).1)).sum):=
  CommonHeadCode.Program.sum_nat_primitive.comp
    (Primrec.list_map ctx_range (Primrec.nat_mul.comp index_coefficient index_value).to₂)

theorem full_basis_variables:Primrec (fun p:EvalContext=>
    (List.range p.1).flatMap (fun j=>(p.2.2.getD j (0,[])).2)):=
  Primrec.list_flatMap ctx_range index_variables

theorem variables_primitive:Primrec (fun p:EvalContext=>variablesAt p.1 p.2.1
    (fun j=>(p.2.2.getD j (0,[])).2)):=by
  have hout:Primrec (fun p:EvalContext=>(List.range p.1).flatMap
      (fun j=>if p.2.1.2.1.getD j 0=0 then [] else (p.2.2.getD j (0,[])).2)):=
    Primrec.list_flatMap ctx_range
      (Primrec.ite (Primrec.eq.comp index_coefficient (Primrec.const (0:Nat))) (Primrec.const []) index_variables).to₂
  have hheads:Primrec (fun p:EvalContext=>p.2.1.2.2.flatMap
      (fun _=>(List.range p.1).flatMap (fun j=>(p.2.2.getD j (0,[])).2))):=
    Primrec.list_flatMap ctx_atoms (full_basis_variables.comp Primrec.fst).to₂
  exact Primrec.list_append.comp hout hheads
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluation.Program
