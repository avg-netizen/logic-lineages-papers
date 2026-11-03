module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCodePrimitiveProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCode.Program
open CommonHeadLargeGuards CommonHeadCompiler IntegerAlgorithms.Proof

theorem mask_primitive:Primrec (fun p:Nat×Nat×List Bool=>maskCode p.1 p.2.1 p.2.2):=by
  let D:=(Nat×Nat×List Bool)×Nat
  have hatom:Primrec (fun p:D=>[(2,p.1.2.1,p.2)]):=
    Primrec.list_cons.comp ((Primrec.const 2).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)) (Primrec.const [])
  have hflag:Primrec (fun p:D=>p.1.2.2.getD p.2 false):=
    (Primrec.list_getD false).comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  have hpick:Primrec₂ (fun p:Nat×Nat×List Bool=>fun j:Nat=>
      if p.2.2.getD j false then [(2,p.2.1,j)] else negative [(2,p.2.1,j)]):=by
    apply (Primrec.cond hflag hatom (negative_primitive.comp hatom)).of_eq
    intro p
    dsimp only
    cases p.1.2.2.getD p.2 false <;> rfl
  exact conjoin_primitive.comp (Primrec.list_map (Primrec.list_range.comp Primrec.fst) hpick)

theorem block_primitive:Primrec (fun p:List Int×Nat×Int=>blockCode p.1 p.2.1 p.2.2):=by
  have hsign:Primrec (fun p:List Bool×(List Int×Int)=>Int.sign (maskCoefficient p.2.1 p.1)):=
    sign_primitive.comp (coefficient_primitive.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
  have hpred:PrimrecRel (fun mask:List Bool=>fun p:List Int×Int=>Int.sign (maskCoefficient p.1 mask)=p.2):=
    Primrec.eq.comp hsign (Primrec.snd.comp Primrec.snd)
  have hmasks:Primrec (fun p:List Int×Nat×Int=>masks p.1.length):=
    masks_primitive.comp (Primrec.list_length.comp Primrec.fst)
  have hparams:Primrec (fun p:List Int×Nat×Int=>(p.1,p.2.2)):=
    Primrec.fst.pair (Primrec.snd.comp Primrec.snd)
  have hfilter:Primrec (fun p:List Int×Nat×Int=>
      (masks p.1.length).filter (fun mask=>Int.sign (maskCoefficient p.1 mask)=p.2.2)):=
    hpred.listFilter.comp hmasks hparams
  have heach:Primrec₂ (fun p:List Int×Nat×Int=>fun mask:List Bool=>maskCode p.1.length p.2.1 mask):=
    mask_primitive.comp ((Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))
  exact disjoin_primitive.comp (Primrec.list_map hfilter heach)

theorem canceled_primitive:Primrec canceledCode:=
  conjoin_primitive.comp (Primrec.list_map (Primrec.list_range.comp Primrec.list_length)
    (block_primitive.comp (Primrec.fst.pair (Primrec.snd.pair (Primrec.const 0)))).to₂)

theorem maximal_primitive:Primrec₂ maximalCode:=by
  let D:=(List Int×Nat)×Nat
  have hatom:Primrec (fun p:D=>[(3,p.1.2,p.2)]):=
    Primrec.list_cons.comp ((Primrec.const 3).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)) (Primrec.const [])
  have hb:Primrec (fun p:D=>blockCode p.1.1 p.2 0):=
    block_primitive.comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.snd.pair (Primrec.const 0)))
  have heach:Primrec₂ (fun p:List Int×Nat=>fun j:Nat=>disjunction (negative [(3,p.2,j)]) (blockCode p.1 j 0)):=
    disjunction_primitive.comp (negative_primitive.comp hatom) hb
  exact conjoin_primitive.comp (Primrec.list_map
    (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)) heach)

theorem sign_primitive_code:Primrec (fun p:Int×List Int×Int=>signCode p.1 p.2.1 p.2.2):=by
  let D:=Int×List Int×Int
  have hk:Primrec (fun p:D=>p.1):=Primrec.fst
  have hcs:Primrec (fun p:D=>p.2.1):=Primrec.fst.comp Primrec.snd
  have hd:Primrec (fun p:D=>p.2.2):=Primrec.snd.comp Primrec.snd
  have hflag:Primrec (fun p:D=>decide (Int.sign p.1=p.2.2)):=
    Primrec.eq.decide.comp (sign_primitive.comp hk) hd
  have hleft:Primrec (fun p:D=>conjunction (constant (decide (Int.sign p.1=p.2.2))) (canceledCode p.2.1)):=
    conjunction_primitive.comp (constant_primitive.comp hflag) (canceled_primitive.comp hcs)
  have heach:Primrec₂ (fun p:D=>fun i:Nat=>conjunction (blockCode p.2.1 i p.2.2) (maximalCode p.2.1 i)):=
    conjunction_primitive.comp
      (block_primitive.comp ((hcs.comp Primrec.fst).pair (Primrec.snd.pair (hd.comp Primrec.fst))))
      (maximal_primitive.comp (hcs.comp Primrec.fst) Primrec.snd)
  have hmany:Primrec (fun p:D=>disjoin ((List.range p.2.1.length).map
      (fun i=>conjunction (blockCode p.2.1 i p.2.2) (maximalCode p.2.1 i)))):=
    disjoin_primitive.comp (Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp hcs)) heach)
  have hright:Primrec (fun p:D=>if p.2.2=0 then constant false else disjoin ((List.range p.2.1.length).map
      (fun i=>conjunction (blockCode p.2.1 i p.2.2) (maximalCode p.2.1 i)))):=
    Primrec.ite (Primrec.eq.comp hd (Primrec.const 0)) (Primrec.const (constant false)) hmany
  exact disjunction_primitive.comp hleft hright

theorem large_primitive:Primrec (fun p:Int×List Int×Int=>largeCode p.1 p.2.1 p.2.2):=by
  have hbound:Primrec₂ (fun p:Int×List Int×Int=>fun i:Nat=>[(4,originalThreshold p.1 p.2.1,i)]):=
    Primrec.list_cons.comp ((Primrec.const 4).pair
      ((threshold_primitive.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd)) (Primrec.const [])
  have hbounds:Primrec (fun p:Int×List Int×Int=>conjoin
      ((List.range p.2.1.length).map (fun i=>[(4,originalThreshold p.1 p.2.1,i)]))):=
    conjoin_primitive.comp (Primrec.list_map
      (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))) hbound)
  exact conjunction_primitive.comp hbounds sign_primitive_code
end LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCode.Program
