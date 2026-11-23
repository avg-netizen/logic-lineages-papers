module
public import LogicLineages.StandardControlCurrent.PolicyIndexedRankedLayerTargets

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedRankedLayer
open ComputableRankedProof (mapGraph mapGraphProgram)
open PolicyIndexedRankedGraph (Matrix)

private theorem passesSuccFirst {A β σ : Type} [Primcodable β]
    (l : β → List β) (assemble : Assembly A β σ) (a : A) (prev : Matrix β σ)
    (s : State β σ) (i : Nat) :
    passes l assemble a prev s (i+1) =
      (advance l assemble a prev s).bind (fun q => passes l assemble a prev q i) := by
  induction i with
  | zero => simp [passes,Part.bind_some_right]
  | succ i ih =>
    change (passes l assemble a prev s (i+1)).bind _ =
      (advance l assemble a prev s).bind (fun q =>
        (passes l assemble a prev q i).bind _)
    rw [ih,Part.bind_assoc]

theorem exactIndexedLayer : ExactIndexedLayer := by
  intro A β σ _ l assemble a g ha nodes prev
  let emit : β → Option (β × σ) := fun b => (g b (mapGraph prev (l b))).map (b, ·)
  have run (nodes : List β) (prior : Matrix β σ) :
      passes l assemble a prev (nodes,prior) nodes.length =
        Part.some ([],prior ++ nodes.filterMap emit) := by
    induction nodes generalizing prior with
    | nil => simp [passes]
    | cons b bs ih =>
      simp only [List.length_cons,passesSuccFirst,advance,ha,Part.map_some,Part.bind_some,ih,
        List.filterMap_cons]
      cases e : g b (mapGraph prev (l b)) <;> simp [emit,e,List.append_assoc]
  change (passes l assemble a prev (nodes,[]) nodes.length).map Prod.snd =
    Part.some (nodes.filterMap emit)
  simp [run]

private theorem optionalRowComputable {β σ : Type} [Primcodable β] [Primcodable σ] :
    Computable (fun x : β × Option σ => (x.2.map (x.1, ·)).toList) :=
  Primrec.optionToList.to_comp.comp
    (Computable.option_map Computable.snd ((Computable.fst.comp Computable.fst).pair Computable.snd).to₂)

private theorem resultComputable {T β σ : Type} [Primcodable T] [Primcodable β] [Primcodable σ]
    {s : T → State β σ} (hs : Computable s) : Computable₂ (fun (p : T × β) (out : Option σ) =>
      ((s p.1).1.tail,(s p.1).2 ++ (out.map (p.2, ·)).toList)) := by
  let U := (T × β) × Option σ
  have input : Computable (fun p : U => p.1.1) := Computable.fst.comp Computable.fst
  have rowInput : Computable (fun p : U => (p.1.2,p.2)) :=
    (Computable.snd.comp Computable.fst).pair Computable.snd
  have state : Computable (fun p : U => s p.1.1) := hs.comp input
  have nodes : Computable (fun p : U => (s p.1.1).1) := Computable.fst.comp state
  have prior : Computable (fun p : U => (s p.1.1).2) := Computable.snd.comp state
  have row : Computable (fun p : U => (p.2.map (p.1.2, ·)).toList) :=
    optionalRowComputable.comp rowInput
  have combined : Computable (fun p : U =>
      ((s p.1.1).1.tail,(s p.1.1).2 ++ (p.2.map (p.1.2, ·)).toList)) :=
    (Primrec.list_tail.to_comp.comp nodes).pair (Primrec.list_append.to_comp.comp prior row)
  exact combined.to₂

private theorem advancePartrec {A β σ : Type} [Primcodable A] [Primcodable β] [Primcodable σ]
    {l : β → List β} {assemble : Assembly A β σ}
    (hl : Primrec l) (ha : Partrec₂ assemble) :
    Partrec (fun p : (A × Matrix β σ) × State β σ => advance l assemble p.1.1 p.1.2 p.2) := by
  let T := (A × Matrix β σ) × State β σ
  have key : Computable (fun p : T => p.1.1) := Computable.fst.comp Computable.fst
  have prev : Computable (fun p : T => p.1.2) := Computable.snd.comp Computable.fst
  have nodes : Computable (fun p : T => p.2.1) := Computable.fst.comp Computable.snd
  have head : Computable (fun p : T => p.2.1[0]?) :=
    Primrec.list_getElem?.to_comp.comp nodes (Computable.const 0)
  have call : Partrec₂ (fun (p : T) (b : β) => assemble p.1.1 (b,mapGraph p.1.2 (l b))) :=
    (ha.comp (key.comp Computable.fst) (Computable.snd.pair
      (mapGraphProgram.to_comp.comp (prev.comp Computable.fst) (hl.to_comp.comp Computable.snd)))).to₂
  have result : Computable₂ (fun (p : T × β) (out : Option σ) =>
      (p.1.2.1.tail,p.1.2.2 ++ (out.map (p.2, ·)).toList)) :=
    resultComputable (Computable.snd : Computable (Prod.snd : T → State β σ))
  have onHead : Partrec₂ (fun (p : T) (b : β) =>
      (assemble p.1.1 (b,mapGraph p.1.2 (l b))).map (fun out =>
        (p.2.1.tail,p.2.2 ++ (out.map (b, ·)).toList))) :=
    (Partrec.map call result).to₂
  have action := Partrec.bind (Computable.ofOption head) onHead
  have flag : Computable (fun p : T => if p.2.1[0]?.isSome then (1 : Nat) else 0) :=
    (Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)).to_comp.comp
      (Primrec.option_isSome.to_comp.comp head)
  apply (Partrec.nat_casesOn_right flag Computable.snd (action.comp Computable.fst).to₂).of_eq
  rintro ⟨⟨a,prev⟩,nodes,prior⟩
  cases nodes <;> simp [advance,Computable.ofOption,Part.bind_some]

private theorem passesRec {A β σ : Type} [Primcodable β]
    (l : β → List β) (assemble : Assembly A β σ) (a : A) (prev : Matrix β σ)
    (initial : State β σ) (n : Nat) :
    n.rec (Part.some initial) (fun _ s => s.bind (advance l assemble a prev)) =
      passes l assemble a prev initial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact congrArg (fun s => s.bind (advance l assemble a prev)) ih

theorem indexedLayerEffectivity : IndexedLayerEffectivity := by
  intro A β σ _ _ _ l assemble hl ha
  let T := A × (List β × Matrix β σ)
  let U := T × (Nat × State β σ)
  have nodes : Computable (fun p : T => p.2.1) := Computable.fst.comp Computable.snd
  have init : Computable (fun p : T => (p.2.1,([] : Matrix β σ))) :=
    nodes.pair (Computable.const [])
  have keyPrev : Computable (fun p : U => (p.1.1,p.1.2.2)) :=
    (Computable.fst.comp Computable.fst).pair
      (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have state : Computable (fun p : U => p.2.2) := Computable.snd.comp Computable.snd
  have step : Partrec₂ (fun (p : T) (v : Nat × State β σ) =>
      advance l assemble p.1 p.2.2 v.2) :=
    ((advancePartrec hl ha).comp (keyPrev.pair state)).to₂
  have hrun := Partrec.nat_rec (Primrec.list_length.to_comp.comp nodes) init.partrec step
  have h := Partrec.map hrun (Computable.snd.comp Computable.snd).to₂
  have hlayer : Partrec (fun p : T => layer l assemble p.1 p.2) := h.of_eq (by
    rintro ⟨a,nodes,prev⟩
    change ((nodes.length.rec (Part.some (nodes,([] : Matrix β σ)))
      (fun _ s => s.bind (advance l assemble a prev))).map Prod.snd) =
      ((passes l assemble a prev (nodes,[]) nodes.length).map Prod.snd)
    rw [passesRec])
  exact hlayer.to₂

end LogicLineages.StandardControlCurrent.PolicyIndexedRankedLayer
