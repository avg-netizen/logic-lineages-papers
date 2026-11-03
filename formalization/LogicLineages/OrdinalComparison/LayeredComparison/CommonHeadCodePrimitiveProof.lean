module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCode.Program
open CommonHeadLargeGuards CommonHeadCompiler
open IntegerAlgorithms.Proof

private theorem quote_primitive (op:Nat):Primrec₂ (fun p q:Code=>p++q++[(op,0,0)]):=
  Primrec.list_append.comp (Primrec.list_append.comp Primrec.fst Primrec.snd) (Primrec.const [(op,0,0)])
theorem constant_primitive:Primrec constant:=Primrec.dom_bool _
theorem conjunction_primitive:Primrec₂ conjunction:=quote_primitive 6
theorem disjunction_primitive:Primrec₂ disjunction:=quote_primitive 7
theorem negative_primitive:Primrec negative:=Primrec.list_append.comp Primrec.id (Primrec.const [(5,0,0)])
theorem conjoin_primitive:Primrec conjoin:=
  Primrec.list_foldr Primrec.id (Primrec.const (constant true))
    (conjunction_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
theorem disjoin_primitive:Primrec disjoin:=
  Primrec.list_foldr Primrec.id (Primrec.const (constant false))
    (disjunction_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

theorem sum_int_primitive:Primrec (fun xs:List Int=>xs.sum):=by
  apply (Primrec.list_foldr Primrec.id (Primrec.const (0:Int))
    (add_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
  intro xs
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [id_eq,List.foldr_cons,List.sum_cons] at ih ⊢
    rw [ih]

theorem sum_nat_primitive:Primrec (fun xs:List Nat=>xs.sum):=by
  apply (Primrec.list_foldr Primrec.id (Primrec.const (0:Nat))
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
  intro xs
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [id_eq,List.foldr_cons,List.sum_cons] at ih ⊢
    rw [ih]

theorem zipWith_primitive {A B C:Type} [Primcodable A] [Primcodable B] [Primcodable C]
    [Inhabited A] [Inhabited B] (f:A→B→C) (hf:Primrec₂ f):Primrec₂ (List.zipWith f):=by
  have hlen:Primrec (fun p:List A×List B=>min p.1.length p.2.length):=
    Primrec.nat_min.comp (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd)
  have hbody:Primrec₂ (fun p:List A×List B=>fun i:Nat=>f (p.1.getD i default) (p.2.getD i default)):=
    hf.comp ((Primrec.list_getD default).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      ((Primrec.list_getD default).comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  apply (Primrec.list_map (Primrec.list_range.comp hlen) hbody).of_eq
  intro p
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hb:i<min p.1.length p.2.length:=by simpa using hi
    have h₁:i<p.1.length:=hb.trans_le (Nat.min_le_left _ _)
    have h₂:i<p.2.length:=hb.trans_le (Nat.min_le_right _ _)
    simp only [List.getElem_map,List.getElem_range,List.getElem_zipWith,
      List.getD_eq_getElem _ _ h₁,List.getD_eq_getElem _ _ h₂]

theorem masks_primitive:Primrec masks:=by
  have hfalse:Primrec (fun xs:List (List Bool)=>xs.map (false::·)):=
    Primrec.list_map Primrec.id (Primrec.list_cons.comp (Primrec.const false) Primrec.snd).to₂
  have htrue:Primrec (fun xs:List (List Bool)=>xs.map (true::·)):=
    Primrec.list_map Primrec.id (Primrec.list_cons.comp (Primrec.const true) Primrec.snd).to₂
  have hstep:Primrec (fun xs:List (List Bool)=>xs.map (false::·)++xs.map (true::·)):=
    Primrec.list_append.comp hfalse htrue
  apply (Primrec.nat_rec' Primrec.id (Primrec.const ([[]]:List (List Bool)))
    (hstep.comp (Primrec.snd.comp Primrec.snd)).to₂).of_eq
  intro n
  induction n <;> simp_all [masks]

theorem coefficient_primitive:Primrec₂ maskCoefficient:=by
  have hpick:Primrec₂ (fun a:Int=>fun b:Bool=>if b then a else 0):=by
    apply (Primrec.cond Primrec.snd Primrec.fst (Primrec.const (0:Int))).of_eq
    intro p
    cases p.2 <;> rfl
  exact sum_int_primitive.comp (zipWith_primitive _ hpick)

theorem threshold_primitive:Primrec₂ originalThreshold:=by
  have hm:Primrec (fun cs:List Int=>(cs.map Int.natAbs).sum):=
    sum_nat_primitive.comp (Primrec.list_map Primrec.id (abs_primitive.comp Primrec.snd).to₂)
  have hc:Primrec (fun p:Int×List Int=>2*(p.2.map Int.natAbs).sum):=Primrec.nat_mul.comp (Primrec.const 2) (hm.comp Primrec.snd)
  have hk:Primrec (fun p:Int×List Int=>4*p.1.natAbs+4):=Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 4) (abs_primitive.comp Primrec.fst)) (Primrec.const 4)
  apply (Primrec.nat_max.comp (Primrec.const 4) (Primrec.nat_max.comp hc hk)).of_eq
  intro p
  simp [originalThreshold,CommonHeadLargeRow.threshold,CommonHeadLargeRow.mass,List.map_map,Function.comp_def]
end LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCode.Program
