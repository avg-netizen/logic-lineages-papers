module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluationValueProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BaseTermProgramInterfacesProof
public import LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraphProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluation.Program
attribute [local irreducible] Nat.sqrt Nat.unpair upperData certificateData valueAt variablesAt

private theorem input_shape:Primrec (fun p:Input=>p.1):=Primrec.fst
private theorem input_tail:Primrec (fun p:Input=>p.2):=Primrec.snd
private theorem input_certificate:Primrec (fun p:Input=>p.2.1):=Primrec.fst.comp input_tail
private theorem input_expression_tail:Primrec (fun p:Input=>p.2.2):=Primrec.snd.comp input_tail
private theorem input_expression:Primrec (fun p:Input=>p.2.2.1):=Primrec.fst.comp input_expression_tail
private theorem input_table:Primrec (fun p:Input=>p.2.2.2):=Primrec.snd.comp input_expression_tail
private theorem input_size:Primrec (fun p:Input=>p.1.getD 0 0):=
  (Primrec.list_getD (0:Nat)).comp input_shape (Primrec.const 0)
private theorem input_shape_tail:Primrec (fun p:Input=>p.1.tail):=Primrec.list_tail.comp input_shape
private theorem input_certificate_data:Primrec (fun p:Input=>certificateData p.2.1):=
  certificateData_primitive.comp input_certificate
private theorem input_lower_certificate:Primrec (fun p:Input=>(certificateData p.2.1).1):=
  Primrec.fst.comp input_certificate_data
private theorem input_basis:Primrec (fun p:Input=>(certificateData p.2.1).2):=
  Primrec.snd.comp input_certificate_data

private abbrev ChildContext:=Input×Nat
private theorem child_origin:Primrec (fun p:ChildContext=>p.1):=Primrec.fst
private theorem child_shape:Primrec (fun p:ChildContext=>p.1.1.tail):=input_shape_tail.comp child_origin
private theorem child_certificate:Primrec (fun p:ChildContext=>(certificateData p.1.2.1).1):=
  input_lower_certificate.comp child_origin
private theorem child_expression:Primrec (fun p:ChildContext=>(certificateData p.1.2.1).2.getD p.2 0):=
  (Primrec.list_getD (0:Nat)).comp (input_basis.comp child_origin) Primrec.snd
private theorem child_table:Primrec (fun p:ChildContext=>p.1.2.2.2):=input_table.comp child_origin
private theorem child_record:Primrec (fun p:ChildContext=>(p.1.1.tail,(certificateData p.1.2.1).1,
    (certificateData p.1.2.1).2.getD p.2 0,p.1.2.2.2)):=
  child_shape.pair (child_certificate.pair (child_expression.pair child_table))
private theorem positive_children:Primrec (fun p:Input=>(List.range (p.1.getD 0 0)).map
    (fun j=>(p.1.tail,(certificateData p.2.1).1,(certificateData p.2.1).2.getD j 0,p.2.2.2))):=
  Primrec.list_map (Primrec.list_range.comp input_size) child_record.to₂
private theorem empty_predicate:PrimrecPred (fun p:Input=>p.1.length=0):=
  Primrec.eq.comp (Primrec.list_length.comp input_shape) (Primrec.const 0)

theorem children_primitive:Primrec children:=by
  apply (Primrec.ite empty_predicate (Primrec.const ([]:List Input)) positive_children).of_eq
  intro p
  cases h:p.1 <;>simp [children,h]

private abbrev Assembly:=Input×List Result
private theorem assembly_origin:Computable (fun p:Assembly=>p.1):=Computable.fst
private theorem assembly_size:Computable (fun p:Assembly=>p.1.1.getD 0 0):=
  input_size.to_comp.comp assembly_origin
private theorem assembly_upper:Computable (fun p:Assembly=>upperData p.1.2.2.1):=
  upperData_primitive.to_comp.comp (input_expression.to_comp.comp assembly_origin)
private theorem assembly_context:Computable (fun p:Assembly=>
    (p.1.1.getD 0 0,upperData p.1.2.2.1,p.2)):=
  assembly_size.pair (assembly_upper.pair Computable.snd)
private theorem assembly_value:Computable (fun p:Assembly=>
    valueAt (p.1.1.getD 0 0) (upperData p.1.2.2.1) (fun j=>(p.2.getD j (0,[])).1)):=
  value_computable.comp assembly_context
private theorem assembly_variables:Computable (fun p:Assembly=>
    variablesAt (p.1.1.getD 0 0) (upperData p.1.2.2.1) (fun j=>(p.2.getD j (0,[])).2)):=
  variables_primitive.to_comp.comp assembly_context
private theorem positive_assembly:Computable (fun p:Assembly=>
    (valueAt (p.1.1.getD 0 0) (upperData p.1.2.2.1) (fun j=>(p.2.getD j (0,[])).1),
     variablesAt (p.1.1.getD 0 0) (upperData p.1.2.2.1) (fun j=>(p.2.getD j (0,[])).2))):=
  assembly_value.pair assembly_variables
private theorem assembly_expression:Computable (fun p:Assembly=>p.1.2.2.1):=
  input_expression.to_comp.comp assembly_origin
private theorem assembly_table:Computable (fun p:Assembly=>p.1.2.2.2):=
  input_table.to_comp.comp assembly_origin
private theorem base_value:Computable (fun p:Assembly=>BaseTermPrograms.valueCode p.1.2.2.1 p.1.2.2.2):=
  BaseTermPrograms.Program.actualComputation.1.comp assembly_expression assembly_table
private theorem base_variables:Computable (fun p:Assembly=>BaseTermPrograms.variablesCode p.1.2.2.1):=
  BaseTermPrograms.Program.actualComputation.2.comp assembly_expression
private theorem base_assembly:Computable (fun p:Assembly=>
    (BaseTermPrograms.valueCode p.1.2.2.1 p.1.2.2.2,BaseTermPrograms.variablesCode p.1.2.2.1)):=
  base_value.pair base_variables
private theorem assembly_empty:Computable (fun p:Assembly=>decide (p.1.1.length=0)):=
  (empty_predicate.decide.to_comp).comp assembly_origin

theorem assemble_computable:Computable₂ assemble:=by
  apply (Computable.cond assembly_empty base_assembly positive_assembly).of_eq
  intro p
  cases h:p.1.1 <;>simp [assemble,h]

theorem numericalInterfaces:Targets.NumericalInterfaces:=⟨children_primitive.to_comp,assemble_computable⟩

theorem allCodeComputation:Targets.AllCodeComputation:=
  (FiniteGraph.Proof.exactDecreasingGraph Input Result children assemble (fun p=>p.1.length)
    children_primitive.to_comp assemble_computable (Primrec.list_length.to_comp.comp input_shape.to_comp)
    joint Proof.finiteCallEquation.1 Proof.finiteCallEquation.2).2
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluation.Program
