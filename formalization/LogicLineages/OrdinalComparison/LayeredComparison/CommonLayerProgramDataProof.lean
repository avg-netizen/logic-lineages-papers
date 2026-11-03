module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerProgramTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCodeInterfacesProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerProgram.Program
open CommonLayerSyntax CommonLayerComparison IntegerAlgorithms.Proof
attribute [local irreducible] Nat.sqrt Nat.unpair rawNormCode

theorem payload_primitive:Primrec payload:=
  Primrec.option_getD.comp (Primrec.decode:Primrec (fun n:Nat=>(Encodable.decode n:Option Payload)))
    (Primrec.const (0,[]))

theorem constant_primitive:Primrec₂ constantCode:=by
  have hz:PrimrecPred (fun p:Nat×Nat=>p.1=0):=
    Primrec.eq.comp Primrec.fst (Primrec.const 0)
  have hn:Primrec (fun p:Nat×Nat=>4*p.2):=Primrec.nat_mul.comp (Primrec.const 4) Primrec.snd
  have hp:Primrec (fun p:Nat×Nat=>Encodable.encode (p.2,([]:List (Nat×Nat)))):=
    Primrec.encode.comp (Primrec.snd.pair (Primrec.const []))
  exact Primrec.ite hz hn hp

private theorem positive_atom:Primrec (fun a:Nat×Nat=>((a.1+1:Int),a.2)):=by
  have hc:Primrec (fun a:Nat×Nat=>(a.1:Int)+1):=
    add_primitive.comp (ofNat_primitive.comp Primrec.fst) (Primrec.const 1)
  exact hc.pair Primrec.snd
private theorem negative_atom:Primrec (fun a:Nat×Nat=>(-((a.1+1:Int)),a.2)):=
  (negate_primitive.comp (Primrec.fst.comp positive_atom)).pair Primrec.snd

private theorem positive_atoms:Primrec (fun xs:List (Nat×Nat)=>xs.map (fun a=>((a.1+1:Int),a.2))):=
  Primrec.list_map Primrec.id (positive_atom.comp Primrec.snd).to₂
private theorem negative_atoms:Primrec (fun xs:List (Nat×Nat)=>xs.map (fun a=>(-((a.1+1:Int)),a.2))):=
  Primrec.list_map Primrec.id (negative_atom.comp Primrec.snd).to₂

theorem atoms_primitive:Primrec₂ signedAtoms:=by
  have he:Primrec (fun p:Nat×Nat=>(payload p.1).2):=
    Primrec.snd.comp (payload_primitive.comp Primrec.fst)
  have hf:Primrec (fun p:Nat×Nat=>(payload p.2).2):=
    Primrec.snd.comp (payload_primitive.comp Primrec.snd)
  exact Primrec.list_append.comp (positive_atoms.comp he) (negative_atoms.comp hf)

theorem coefficients_primitive:Primrec₂ rowCoefficients:=
  Primrec.list_map atoms_primitive (Primrec.fst.comp Primrec.snd).to₂

theorem arguments_primitive:Primrec₂ rowArguments:=
  Primrec.list_map atoms_primitive (Primrec.snd.comp Primrec.snd).to₂

theorem row_constant_primitive:Primrec₂ rowConstant:=by
  have he:Primrec (fun p:Nat×Nat=>((payload p.1).1:Int)):=
    ofNat_primitive.comp (Primrec.fst.comp (payload_primitive.comp Primrec.fst))
  have hf:Primrec (fun p:Nat×Nat=>((payload p.2).1:Int)):=
    ofNat_primitive.comp (Primrec.fst.comp (payload_primitive.comp Primrec.snd))
  exact add_primitive.comp he (negate_primitive.comp hf)

theorem raw_norm_primitive:Primrec rawNormCode:=Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive

theorem base_code_primitive:Primrec (fun p:Nat×Nat×Int=>baseCode p.1 p.2.1 p.2.2):=by
  let D:=Nat×Nat×Int
  have he:Primrec (fun p:D=>p.1):=Primrec.fst
  have hf:Primrec (fun p:D=>p.2.1):=Primrec.fst.comp Primrec.snd
  have hd:Primrec (fun p:D=>p.2.2):=Primrec.snd.comp Primrec.snd
  have eqcode:Primrec (fun p:D=>[(2,p.1,p.2.1)]):=
    Primrec.list_cons.comp ((Primrec.const 2).pair (he.pair hf)) (Primrec.const [])
  have ltcode:Primrec (fun p:D=>[(3,p.1,p.2.1)]):=
    Primrec.list_cons.comp ((Primrec.const 3).pair (he.pair hf)) (Primrec.const [])
  have gtcode:Primrec (fun p:D=>[(3,p.2.1,p.1)]):=
    Primrec.list_cons.comp ((Primrec.const 3).pair (hf.pair he)) (Primrec.const [])
  exact Primrec.ite (Primrec.eq.comp hd (Primrec.const (0:Int))) eqcode
    (Primrec.ite (Primrec.eq.comp hd (Primrec.const (-1:Int))) ltcode
      (Primrec.ite (Primrec.eq.comp hd (Primrec.const (1:Int))) gtcode (Primrec.const [(0,0,0)])))
end LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerProgram.Program
