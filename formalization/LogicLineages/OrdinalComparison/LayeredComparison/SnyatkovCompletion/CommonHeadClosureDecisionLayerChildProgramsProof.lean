module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureDecisionLayerDataProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureLayerPrograms
open CommonLayerProgram CommonLayerSyntax CommonLayerComparison
private abbrev Input := CommonLayerProgram.Input
private abbrev Code := CommonLayerProgram.Code
attribute [local irreducible] Nat.sqrt Nat.unpair constantCode rawNormCode

theorem getD_primitive:Primrec (fun p:List Nat×Nat×Nat=>p.1.getD p.2.1 p.2.2):=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

abbrev Context:=List Nat×Nat×List Nat×CommonHeadCompiler.Instruction
private theorem context_heads:Primrec (fun p:Context=>p.1):=Primrec.fst
private theorem context_norm:Primrec (fun p:Context=>p.2.1):=Primrec.fst.comp Primrec.snd
private theorem context_tail:Primrec (fun p:Context=>p.2.2):=Primrec.snd.comp Primrec.snd
private theorem context_args:Primrec (fun p:Context=>p.2.2.1):=Primrec.fst.comp context_tail
private theorem context_instruction:Primrec (fun p:Context=>p.2.2.2):=Primrec.snd.comp context_tail
private theorem context_tag:Primrec (fun p:Context=>p.2.2.2.1):=Primrec.fst.comp context_instruction
private theorem context_operands:Primrec (fun p:Context=>p.2.2.2.2):=Primrec.snd.comp context_instruction
private theorem context_left:Primrec (fun p:Context=>p.2.2.2.2.1):=Primrec.fst.comp context_operands
private theorem context_right:Primrec (fun p:Context=>p.2.2.2.2.2):=Primrec.snd.comp context_operands
private theorem context_zero:Primrec (fun p:Context=>constantCode p.1.length 0):=
  constant_primitive.comp (Primrec.list_length.comp context_heads) (Primrec.const 0)
private theorem context_first_arg:Primrec (fun p:Context=>p.2.2.1.getD p.2.2.2.2.1 (constantCode p.1.length 0)):=
  getD_primitive.comp (context_args.pair (context_left.pair context_zero))
private theorem context_second_arg:Primrec (fun p:Context=>p.2.2.1.getD p.2.2.2.2.2 (constantCode p.1.length 0)):=
  getD_primitive.comp (context_args.pair (context_right.pair context_zero))
private theorem context_bound:Primrec (fun p:Context=>constantCode p.1.length (p.2.2.2.2.1-p.2.1)):=
  constant_primitive.comp (Primrec.list_length.comp context_heads) (Primrec.nat_sub.comp context_left context_norm)
private theorem equality_child:Primrec (fun p:Context=>(p.1,
    p.2.2.1.getD p.2.2.2.2.1 (constantCode p.1.length 0),
    p.2.2.1.getD p.2.2.2.2.2 (constantCode p.1.length 0),(0:Int))):=
  context_heads.pair (context_first_arg.pair (context_second_arg.pair (Primrec.const 0)))
private theorem order_child:Primrec (fun p:Context=>(p.1,
    p.2.2.1.getD p.2.2.2.2.1 (constantCode p.1.length 0),
    p.2.2.1.getD p.2.2.2.2.2 (constantCode p.1.length 0),(-1:Int))):=
  context_heads.pair (context_first_arg.pair (context_second_arg.pair (Primrec.const (-1))))
private theorem bound_child:Primrec (fun p:Context=>(p.1,
    p.2.2.1.getD p.2.2.2.2.2 (constantCode p.1.length 0),
    constantCode p.1.length (p.2.2.2.2.1-p.2.1),(-1:Int))):=
  context_heads.pair (context_second_arg.pair (context_bound.pair (Primrec.const (-1))))
private theorem dummy_child:Primrec (fun p:Context=>(p.1,constantCode p.1.length 0,
    constantCode p.1.length 0,(0:Int))):=
  context_heads.pair (context_zero.pair (context_zero.pair (Primrec.const 0)))

theorem child_primitive:Primrec (fun p:Context=>child p.1 p.2.1 p.2.2.1 p.2.2.2):=
  Primrec.ite (Primrec.eq.comp context_tag (Primrec.const (2:Nat))) equality_child
    (Primrec.ite (Primrec.eq.comp context_tag (Primrec.const (3:Nat))) order_child
      (Primrec.ite (Primrec.eq.comp context_tag (Primrec.const (4:Nat))) bound_child dummy_child))

theorem instruction_primitive:Primrec (fun p:Nat×CommonHeadCompiler.Instruction×Code=>
    instructionCode p.1 p.2.1 p.2.2):=by
  let D:=Nat×CommonHeadCompiler.Instruction×Code
  have hn:Primrec (fun p:D=>p.1):=Primrec.fst
  have hq:Primrec (fun p:D=>p.2.1):=Primrec.fst.comp Primrec.snd
  have hr:Primrec (fun p:D=>p.2.2):=Primrec.snd.comp Primrec.snd
  have ht:Primrec (fun p:D=>p.2.1.1):=Primrec.fst.comp hq
  have hc:Primrec (fun p:D=>p.2.1.2.1):=Primrec.fst.comp (Primrec.snd.comp hq)
  have hs:Primrec (fun p:D=>[p.2.1]):=Primrec.list_cons.comp hq (Primrec.const [])
  have hneg:Primrec (fun p:D=>p.2.2++[(5,0,0)]):=
    Primrec.list_append.comp hr (Primrec.const [(5,0,0)])
  have hb:Primrec (fun p:D=>if p.2.1.2.1≤p.1 then [(1,0,0)] else p.2.2++[(5,0,0)]):=
    Primrec.ite (Primrec.nat_le.comp hc hn) (Primrec.const [(1,0,0)]) hneg
  exact Primrec.ite (Primrec.eq.comp ht (Primrec.const (2:Nat))) hr
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const (3:Nat))) hr
      (Primrec.ite (Primrec.eq.comp ht (Primrec.const (4:Nat))) hb hs))
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureLayerPrograms
