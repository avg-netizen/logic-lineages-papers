module
public import LogicLineages.OrdinalComparison.LayeredComparison.BaseTermProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationGraphProof
public import LogicLineages.OrdinalComparison.ControlComputability
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluation.Base
open BaseTermPrograms
attribute [local irreducible] Nat.sqrt Nat.unpair Phi

private theorem tag_program:Primrec (fun p:Input=>p.1%4):=
  Primrec.nat_mod.comp Primrec.fst (Primrec.const 4)
private theorem quotient_program:Primrec (fun p:Input=>p.1/4):=
  Primrec.nat_div.comp Primrec.fst (Primrec.const 4)
private theorem left_code:Primrec (fun p:Input=>(p.1/4).unpair.1):=
  Primrec.fst.comp (Primrec.unpair.comp quotient_program)
private theorem right_code:Primrec (fun p:Input=>(p.1/4).unpair.2):=
  Primrec.snd.comp (Primrec.unpair.comp quotient_program)
private theorem add_children:Primrec (fun p:Input=>[((p.1/4).unpair.1,p.2),((p.1/4).unpair.2,p.2)]):=
  Primrec.list_cons.comp (left_code.pair Primrec.snd)
    (Primrec.list_cons.comp (right_code.pair Primrec.snd) (Primrec.const []))
private theorem phi_children:Primrec (fun p:Input=>[(p.1/4,p.2)]):=
  Primrec.list_cons.comp (quotient_program.pair Primrec.snd) (Primrec.const [])

theorem children_primitive:Primrec children:=
  Primrec.ite (Primrec.eq.comp tag_program (Primrec.const (2:Nat))) add_children
    (Primrec.ite (Primrec.eq.comp tag_program (Primrec.const (3:Nat))) phi_children (Primrec.const []))

private abbrev Context:=Input×List Result
private theorem source_program:Primrec (fun p:Context=>p.1):=Primrec.fst
private theorem table_program:Primrec (fun p:Context=>p.1.2):=Primrec.snd.comp source_program
private theorem results_program:Primrec (fun p:Context=>p.2):=Primrec.snd
private theorem first_result:Primrec (fun p:Context=>p.2.getD 0 (0,[])):=
  (Primrec.list_getD ((0,[]):Result)).comp results_program (Primrec.const 0)
private theorem second_result:Primrec (fun p:Context=>p.2.getD 1 (0,[])):=
  (Primrec.list_getD ((0,[]):Result)).comp results_program (Primrec.const 1)
private theorem first_value:Primrec (fun p:Context=>(p.2.getD 0 (0,[])).1):=Primrec.fst.comp first_result
private theorem second_value:Primrec (fun p:Context=>(p.2.getD 1 (0,[])).1):=Primrec.fst.comp second_result
private theorem first_variables:Primrec (fun p:Context=>(p.2.getD 0 (0,[])).2):=Primrec.snd.comp first_result
private theorem second_variables:Primrec (fun p:Context=>(p.2.getD 1 (0,[])).2):=Primrec.snd.comp second_result
private theorem variable_value:Primrec (fun p:Context=>valuation p.1.2 (p.1.1/4)):=
  (Primrec.list_getD (1:Nat)).comp table_program (quotient_program.comp source_program)
private theorem numeral_case:Primrec (fun p:Context=>(p.1.1/4,([]:List Nat))):=
  (quotient_program.comp source_program).pair (Primrec.const [])
private theorem variable_case:Primrec (fun p:Context=>(valuation p.1.2 (p.1.1/4),[p.1.1/4])):=
  variable_value.pair (Primrec.list_cons.comp (quotient_program.comp source_program) (Primrec.const []))
private theorem add_case:Primrec (fun p:Context=>((p.2.getD 0 (0,[])).1+(p.2.getD 1 (0,[])).1,
    (p.2.getD 0 (0,[])).2++(p.2.getD 1 (0,[])).2)):=
  (Primrec.nat_add.comp first_value second_value).pair
    (Primrec.list_append.comp first_variables second_variables)
private theorem phi_case:Primrec (fun p:Context=>(Phi (p.2.getD 0 (0,[])).1,(p.2.getD 0 (0,[])).2)):=
  (Phi_primrec.comp first_value).pair first_variables

theorem assemble_primitive:Primrec₂ assemble:=
  Primrec.ite (Primrec.eq.comp (tag_program.comp source_program) (Primrec.const (0:Nat))) numeral_case
    (Primrec.ite (Primrec.eq.comp (tag_program.comp source_program) (Primrec.const (1:Nat))) variable_case
      (Primrec.ite (Primrec.eq.comp (tag_program.comp source_program) (Primrec.const (2:Nat))) add_case phi_case))

theorem numericalInterfaces:BaseTermPrograms.Targets.NumericalInterfaces:=⟨children_primitive.to_comp,assemble_primitive.to_comp⟩

theorem joint_computable:Computable joint:=
  (Graph.exactDecreasingGraph Input Result children assemble Prod.fst
    children_primitive.to_comp assemble_primitive.to_comp Computable.fst joint
    BaseTermPrograms.Proof.finiteCallEquation.1 BaseTermPrograms.Proof.finiteCallEquation.2).2

theorem actualComputation:BaseTermPrograms.Targets.ActualComputation:=by
  refine ⟨Computable.fst.comp joint_computable,?_⟩
  exact (Computable.snd.comp joint_computable).comp (Computable.id.pair (Computable.const ([]:Table)))
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluation.Base
