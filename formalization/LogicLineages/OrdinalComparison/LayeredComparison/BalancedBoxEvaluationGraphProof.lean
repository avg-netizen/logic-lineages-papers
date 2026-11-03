module
public import LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraphCorrectnessProof
public import Mathlib.Data.List.GetD
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluation.Graph
open FiniteGraph

/-! Narrow proof reuse for the unchanged finite-frontier graph. The elementary
fold proofs and computation argument are reproduced here to avoid the broad
comparison-assembly import closure; graph correctness is reused directly. -/

private theorem fold_prefix {α β : Type} (xs : List α) (default : α) (step : β → α → β) (init : β)
    (n : Nat) (hn : n≤xs.length) :
    Nat.rec init (fun i previous => step previous (xs.getD i default)) n=(xs.take n).foldl step init := by
  induction n with
  | zero => simp
  | succ n ih =>
    change step (Nat.rec init (fun i previous => step previous (xs.getD i default)) n) (xs.getD n default)=_
    rw [ih (by omega),List.take_succ_eq_append_getElem (by omega),List.foldl_append,
      List.foldl_cons,List.foldl_nil,List.getD_eq_getElem xs default (by omega)]

theorem computable_foldl {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]
    (default : β) {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldl (fun state item => h a (state,item)) (g a)) := by
  have hitem : Computable (fun p : α × (Nat × σ) => (f p.1).getD p.2.1 default) :=
    (Primrec.list_getD default).to_comp.comp (hf.comp Computable.fst) (Computable.fst.comp Computable.snd)
  have hstep : Computable₂ (fun a : α => fun state : Nat × σ => h a (state.2,(f a).getD state.1 default)) :=
    hh.comp Computable.fst ((Computable.snd.comp Computable.snd).pair hitem)
  apply (Computable.nat_rec (Computable.list_length.comp hf) hg hstep).of_eq
  intro a
  rw [fold_prefix (f a) default (fun state item => h a (state,item)) (g a) (f a).length le_rfl]
  simp only [List.take_length]

theorem computable_foldr {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]
    (default : β) {f : α → List β} {g : α → σ} {h : α → β × σ → σ}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldr (fun item state => h a (item,state)) (g a)) := by
  have hs : Computable₂ (fun a : α => fun state : σ × β => h a (state.2,state.1)) :=
    hh.comp Computable.fst ((Computable.snd.comp Computable.snd).pair (Computable.fst.comp Computable.snd))
  apply (computable_foldl default (Computable.list_reverse.comp hf) hg hs).of_eq
  intro a
  rw [List.foldr_eq_foldl_reverse]



private theorem map_program {X Y Z:Type} [Primcodable X] [Primcodable Y] [Primcodable Z] [Inhabited Y]
    {xs:X→List Y} {f:X→Y→Z} (hx:Computable xs) (hf:Computable₂ f):
    Computable (fun x=>(xs x).map (f x)):=by
  have hs:Computable₂ (fun x:X=>fun state:Y×List Z=>f x state.1::state.2):=
    Primrec.list_cons.to_comp.comp (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  apply (computable_foldr default hx (Computable.const []) hs).of_eq
  intro x
  induction xs x with
  | nil=>rfl
  | cons y ys ih=>simp only [List.foldr_cons,List.map_cons,ih]

private theorem flatMap_program {X Y Z:Type} [Primcodable X] [Primcodable Y] [Primcodable Z] [Inhabited Y]
    {xs:X→List Y} {f:X→Y→List Z} (hx:Computable xs) (hf:Computable₂ f):
    Computable (fun x=>(xs x).flatMap (f x)):=by
  have hs:Computable₂ (fun x:X=>fun state:Y×List Z=>f x state.1++state.2):=
    Primrec.list_append.to_comp.comp (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  apply (computable_foldr default hx (Computable.const []) hs).of_eq
  intro x
  induction xs x with
  | nil=>rfl
  | cons y ys ih=>simp only [List.foldr_cons,List.flatMap_cons,ih]

private theorem filterMap_program {X Y Z:Type} [Primcodable X] [Primcodable Y] [Primcodable Z] [Inhabited Y]
    {xs:X→List Y} {f:X→Y→Option Z} (hx:Computable xs) (hf:Computable₂ f):
    Computable (fun x=>(xs x).filterMap (f x)):=by
  apply (flatMap_program hx (Primrec.optionToList.to_comp.comp hf).to₂).of_eq
  intro x
  induction xs x with
  | nil=>rfl
  | cons y ys ih=>cases he:f x y <;> simp [he,ih]

theorem frontier_program {A:Type} [Primcodable A] [Inhabited A]
    (children:A→List A) (hc:Computable children):Computable₂ (frontier children):=by
  have hs:Computable (fun xs:List A=>xs.flatMap children):=
    flatMap_program Computable.id (hc.comp Computable.snd)
  have hi:Computable (fun p:A×Nat=>[p.1]):=
    Primrec.list_cons.to_comp.comp Computable.fst (Computable.const [])
  have hstep:Computable₂ (fun (_:A×Nat)=>fun state:Nat×List A=>state.2.flatMap children):=
    hs.comp (Computable.snd.comp Computable.snd)
  apply (Computable.nat_rec Computable.snd hi hstep).of_eq
  intro p
  induction p.2 with
  | zero=>rfl
  | succ n ih=>
    change (Nat.rec (motive:=fun _=>List A) [p.1] (fun _ xs=>xs.flatMap children) n).flatMap children=_
    rw [ih]
    exact (Function.iterate_succ_apply' _ _ _).symm

theorem uniformGraph : FiniteGraph.Targets.UniformGraph:=by
  classical
  intro A B _ _ _ children assemble μ hc ha hm
  by_cases hA:Nonempty A
  · letI:Inhabited A:=Classical.inhabited_of_nonempty hA
    let D:=A×(Nat×List (A×B))
    have hparents:Computable (fun p:D=>frontier children p.1 (μ p.1-p.2.1)):=
      (frontier_program children hc).comp Computable.fst
        (Primrec.nat_sub.to_comp.comp (hm.comp Computable.fst) (Computable.fst.comp Computable.snd))
    have hprev:Computable (fun p:D×A=>p.1.2.2):=
      Computable.snd.comp (Computable.snd.comp Computable.fst)
    have hvalues:Computable (fun p:D×A=>(children p.2).filterMap (fun c=>p.1.2.2.lookup c)):=
      filterMap_program (hc.comp Computable.snd)
        (Primrec.listLookup.to_comp.comp Computable.snd (hprev.comp Computable.fst))
    have heach:Computable₂ (fun p:D=>fun b:A=>(b,assemble b ((children b).filterMap (fun c=>p.2.2.lookup c)))):=
      Computable.snd.pair (ha.comp Computable.snd hvalues)
    have hstep:Computable (fun p:D=>
        (frontier children p.1 (μ p.1-p.2.1)).map (fun b=>
          (b,assemble b ((children b).filterMap (fun c=>p.2.2.lookup c))))) :=
      map_program hparents heach
    let F:A→Nat→List (A×B)→List (A×B):=fun a n prev=>
      (frontier children a (μ a-n)).map (fun b=>
        (b,assemble b ((children b).filterMap (fun c=>prev.lookup c))))
    have hinA:Computable (fun p:(A×Nat)×(Nat×List (A×B))=>p.1.1):=
      Computable.fst.comp Computable.fst
    have hinState:Computable (fun p:(A×Nat)×(Nat×List (A×B))=>p.2):=Computable.snd
    have hbody:Computable₂ (fun p:A×Nat=>fun state:Nat×List (A×B)=>F p.1 state.1 state.2):=
      (hstep.comp (hinA.pair hinState)).to₂
    have hrec:Computable (fun p:A×Nat=>Nat.rec (motive:=fun _=>List (A×B)) [] (F p.1) p.2):=
      Computable.nat_rec Computable.snd (Computable.const []) hbody
    apply hrec.of_eq
    intro p
    induction p.2 with
    | zero=>rfl
    | succ n ih=>
      change F p.1 n (Nat.rec (motive:=fun _=>List (A×B)) [] (F p.1) n)=_
      rw [ih]
      rfl
  · letI:IsEmpty A:=⟨fun a=>hA ⟨a⟩⟩
    apply (Computable.const ([]:List (A×B))).of_eq
    intro p
    exact isEmptyElim p.1

theorem exactDecreasingGraph : FiniteGraph.Targets.ExactDecreasingGraph:=by
  intro A B _ _ _ _ children assemble μ hc ha hm f hd hf
  have hroot:∀a,graph children assemble μ a (μ a+1)=[(a,f a)]:=
    FiniteGraph.Proof.graph_root children assemble μ f hd hf
  have hg:Computable (fun a:A=>graph children assemble μ a (μ a+1)):=
    (uniformGraph A B children assemble μ hc ha hm).comp Computable.id
      (Primrec.succ.to_comp.comp hm)
  have hout:Computable (fun a:A=>(graph children assemble μ a (μ a+1)).head?.map Prod.snd):=
    Computable.option_map (Primrec.list_head?.to_comp.comp hg) (Computable.snd.comp Computable.snd)
  have hget:Computable (fun a:A=>((graph children assemble μ a (μ a+1)).head?.map Prod.snd).getD default):=
    Computable.option_getD hout (Computable.const default)
  exact ⟨hroot,hget.of_eq (fun a=>by simp only [hroot,List.head?_cons,Option.map_some,Option.getD_some])⟩
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluation.Graph
