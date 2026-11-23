module
public import LogicLineages.StandardControlCurrent.PolicyIndexedRankedLayerTargets
import Mathlib.Computability.RE

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

private def finishOut {β σ : Type} (x : State β σ × β × Option σ) : State β σ :=
  (x.1.1.tail,x.1.2 ++ (x.2.2.map (x.2.1, ·)).toList)

private theorem finishOutComputable {β σ : Type} [Primcodable β] [Primcodable σ] :
    Computable (finishOut : State β σ × β × Option σ → State β σ) := by
  let U := State β σ × β × Option σ
  have nodes : Computable (fun p : U => p.1.1) := Computable.fst.comp Computable.fst
  have old : Computable (fun p : U => p.1.2) := Computable.snd.comp Computable.fst
  have input : Computable (fun p : U => p.2) := Computable.snd
  have row : Computable (fun p : U => (p.2.2.map (p.2.1, ·)).toList) :=
    optionalRowComputable.comp input
  have tail : Computable (fun p : U => p.1.1.tail) := Primrec.list_tail.to_comp.comp nodes
  have add : Computable (fun p : U => p.1.2 ++ (p.2.2.map (p.2.1, ·)).toList) :=
    Primrec.list_append.to_comp.comp old row
  exact tail.pair add

private theorem chooseHead {T β V : Type} [Primcodable T] [Primcodable β] [Primcodable V]
    {head : T → Option β} {missing : T → V} {found : T → β → Part V}
    (hh : Computable head) (hm : Computable missing) (hf : Partrec₂ found) :
    Partrec (fun p => match head p with
      | none => Part.some (missing p)
      | some b => found p b) := by
  have call := Partrec.bind (Computable.ofOption hh) hf
  apply (Partrec.cond (Primrec.option_isSome.to_comp.comp hh) call hm.partrec).of_eq
  intro p
  cases e : head p <;> simp [e,Part.bind_some]

private abbrev AdvanceIn (A β σ : Type) := (A × Matrix β σ) × State β σ

private theorem headAssembly {A β σ : Type} [Primcodable A] [Primcodable β] [Primcodable σ]
    {l : β → List β} {assemble : Assembly A β σ}
    (hl : Primrec l) (ha : Partrec₂ assemble) :
    Partrec₂ (fun (p : AdvanceIn A β σ) (b : β) =>
      assemble p.1.1 (b,mapGraph p.1.2 (l b))) := by
  let U := AdvanceIn A β σ × β
  have input : Computable (fun p : U => p.1.1) := Computable.fst.comp Computable.fst
  have key : Computable (fun p : U => p.1.1.1) := Computable.fst.comp input
  have prev : Computable (fun p : U => p.1.1.2) := Computable.snd.comp input
  have node : Computable (fun p : U => p.2) := Computable.snd
  have values : Computable (fun p : U => mapGraph p.1.1.2 (l p.2)) :=
    mapGraphProgram.to_comp.comp prev (hl.to_comp.comp node)
  exact (ha.comp key (node.pair values)).to₂

private theorem headFinish {A β σ : Type} [Primcodable A] [Primcodable β] [Primcodable σ] :
    Computable₂ (fun (p : AdvanceIn A β σ × β) (out : Option σ) =>
      finishOut (p.1.2,p.2,out)) := by
  let U := (AdvanceIn A β σ × β) × Option σ
  have pairIn : Computable (fun p : U => (p.1.2,p.2)) :=
    (Computable.snd.comp Computable.fst).pair Computable.snd
  have state : Computable (fun p : U => p.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  exact (finishOutComputable.comp (state.pair pairIn)).to₂

private theorem advancePartrec {A β σ : Type} [Primcodable A] [Primcodable β] [Primcodable σ]
    {l : β → List β} {assemble : Assembly A β σ}
    (hl : Primrec l) (ha : Partrec₂ assemble) :
    Partrec (fun p : AdvanceIn A β σ => advance l assemble p.1.1 p.1.2 p.2) := by
  let T := AdvanceIn A β σ
  have nodes : Computable (fun p : T => p.2.1) := Computable.fst.comp Computable.snd
  have head : Computable (fun p : T => p.2.1[0]?) :=
    Primrec.list_getElem?.to_comp.comp nodes (Computable.const 0)
  have found : Partrec₂ (fun (p : T) (b : β) =>
      (assemble p.1.1 (b,mapGraph p.1.2 (l b))).map (fun out => finishOut (p.2,b,out))) :=
    (Partrec.map (headAssembly hl ha)
      (headFinish : Computable₂ (fun (p : T × β) (out : Option σ) =>
        finishOut (p.1.2,p.2,out)))).to₂
  exact (chooseHead head Computable.snd found).of_eq (by
    rintro ⟨⟨a,prev⟩,nodes,prior⟩
    cases nodes <;> rfl)

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
    exact congrArg (fun x : Part (State β σ) => x.map Prod.snd)
      (passesRec l assemble a prev (nodes,[]) nodes.length))
  exact hlayer.to₂

end LogicLineages.StandardControlCurrent.PolicyIndexedRankedLayer
