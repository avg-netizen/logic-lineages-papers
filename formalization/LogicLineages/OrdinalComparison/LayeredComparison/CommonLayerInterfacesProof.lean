module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerChildProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerProgram.Program
open CommonLayerSyntax CommonLayerComparison CommonHeadCompiler
attribute [local irreducible] Nat.sqrt Nat.unpair rawNormCode constantCode child instructionCode

private theorem map_program {A B C:Type} [Primcodable A] [Primcodable B] [Primcodable C] [Inhabited B]
    {xs:A→List B} {f:A→B→C} (hx:Computable xs) (hf:Computable₂ f):
    Computable (fun a=>(xs a).map (f a)):=by
  have hs:Computable₂ (fun a:A=>fun p:B×List C=>f a p.1::p.2):=
    Primrec.list_cons.to_comp.comp (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  apply (ComparisonAssembly.computable_foldr default hx (Computable.const []) hs).of_eq
  intro a
  induction xs a with
  | nil=>rfl
  | cons b bs ih=>simp only [List.foldr_cons,List.map_cons,ih]

private theorem heads_program:Computable (fun a:Input=>a.1):=Computable.fst
private theorem left_program:Computable (fun a:Input=>a.2.1):=Computable.fst.comp Computable.snd
private theorem right_tail:Computable (fun a:Input=>a.2.2):=Computable.snd.comp Computable.snd
private theorem right_program:Computable (fun a:Input=>a.2.2.1):=Computable.fst.comp right_tail
private theorem desired_program:Computable (fun a:Input=>a.2.2.2):=Computable.snd.comp right_tail
private theorem tail_program:Computable (fun a:Input=>a.1.tail):=Primrec.list_tail.to_comp.comp heads_program
private theorem head_program:Computable (fun a:Input=>a.1.getD 0 0):=
  (Primrec.list_getD (0:Nat)).to_comp.comp heads_program (Computable.const 0)
private theorem norm_program:Computable (fun a:Input=>rawNormCode (a.1.getD 0 0)):=
  raw_norm_primitive.to_comp.comp head_program
private theorem arguments_program:Computable (fun a:Input=>rowArguments a.2.1 a.2.2.1):=
  arguments_primitive.to_comp.comp left_program right_program
private theorem coefficients_program:Computable (fun a:Input=>rowCoefficients a.2.1 a.2.2.1):=
  coefficients_primitive.to_comp.comp left_program right_program
private theorem constant_program:Computable (fun a:Input=>rowConstant a.2.1 a.2.2.1):=
  row_constant_primitive.to_comp.comp left_program right_program
private theorem row_parameters:Computable (fun a:Input=>(a.1.getD 0 0,
    rowConstant a.2.1 a.2.2.1,rowCoefficients a.2.1 a.2.2.1,a.2.2.2)):=
  head_program.pair (constant_program.pair (coefficients_program.pair desired_program))
private theorem row_program:Computable (fun a:Input=>
    rowCode (a.1.getD 0 0) a.2.1 a.2.2.1 a.2.2.2):=
  CommonHeadCode.Program.allCodeEffectivity.comp row_parameters
private theorem empty_program:Computable (fun a:Input=>decide (a.1.length=0)):=
  Primrec.eq.decide.to_comp.comp (Primrec.list_length.to_comp.comp heads_program) (Computable.const 0)

private theorem child_context:Computable (fun p:Input×Instruction=>(p.1.1.tail,
    rawNormCode (p.1.1.getD 0 0),rowArguments p.1.2.1 p.1.2.2.1,p.2)):=
  (tail_program.comp Computable.fst).pair ((norm_program.comp Computable.fst).pair
    ((arguments_program.comp Computable.fst).pair Computable.snd))
private theorem each_child:Computable₂ (fun a:Input=>fun q:Instruction=>
    child a.1.tail (rawNormCode (a.1.getD 0 0)) (rowArguments a.2.1 a.2.2.1) q):=
  child_primitive.to_comp.comp child_context
private theorem nonempty_children:Computable (fun a:Input=>
    (rowCode (a.1.getD 0 0) a.2.1 a.2.2.1 a.2.2.2).map
      (child a.1.tail (rawNormCode (a.1.getD 0 0)) (rowArguments a.2.1 a.2.2.1))):=
  map_program row_program each_child

theorem children_computable:Computable children:=by
  apply (Computable.cond empty_program (Computable.const ([]:List Input)) nonempty_children).of_eq
  intro a
  cases h:a.1 <;>simp [children,h,rowCode]

private theorem pairs_primitive:Primrec₂ (fun qs:List Instruction=>fun rs:List Code=>
    qs.zipWith (fun q r=>(q,r)) rs):=
  CommonHeadCode.Program.zipWith_primitive _ Primrec.id

private abbrev Assembly:=Input×List Code
private theorem assembly_pairs:Computable (fun p:Assembly=>
    (rowCode (p.1.1.getD 0 0) p.1.2.1 p.1.2.2.1 p.1.2.2.2).zipWith
      (fun q r=>(q,r)) p.2):=
  pairs_primitive.to_comp.comp (row_program.comp Computable.fst) Computable.snd
private theorem instruction_context:Computable (fun p:Assembly×(Instruction×Code)=>
    (rawNormCode (p.1.1.1.getD 0 0),p.2.1,p.2.2)):=
  (norm_program.comp (Computable.fst.comp Computable.fst)).pair
    ((Computable.fst.comp Computable.snd).pair (Computable.snd.comp Computable.snd))
private theorem each_instruction:Computable₂ (fun p:Assembly=>fun q:Instruction×Code=>
    instructionCode (rawNormCode (p.1.1.getD 0 0)) q.1 q.2):=
  instruction_primitive.to_comp.comp instruction_context
private theorem assembled_nonempty:Computable (fun p:Assembly=>
    ((rowCode (p.1.1.getD 0 0) p.1.2.1 p.1.2.2.1 p.1.2.2.2).zipWith
      (instructionCode (rawNormCode (p.1.1.getD 0 0))) p.2).flatten):=by
  apply (Primrec.list_flatten.to_comp.comp (map_program assembly_pairs each_instruction)).of_eq
  intro p
  rw [List.map_zipWith]
private theorem base_parameters:Computable (fun a:Input=>(a.2.1,a.2.2.1,a.2.2.2)):=
  left_program.pair (right_program.pair desired_program)
private theorem assembled_empty:Computable (fun p:Assembly=>baseCode p.1.2.1 p.1.2.2.1 p.1.2.2.2):=
  base_code_primitive.to_comp.comp (base_parameters.comp Computable.fst)

theorem assemble_computable:Computable₂ assemble:=by
  apply (Computable.cond (empty_program.comp Computable.fst) assembled_empty assembled_nonempty).of_eq
  intro p
  cases h:p.1.1 <;>simp [assemble,h,rowCode]

theorem numericInterfaces:Targets.NumericalInterfaces:=
  ⟨children_computable,assemble_computable,Primrec.list_length.to_comp.comp heads_program⟩
end LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerProgram.Program
