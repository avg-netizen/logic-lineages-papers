module
public import LogicLineages.StandardControlCurrent.PolicyIndexedPartialTargets
import LogicLineages.StandardControlCurrent.PolicyIndexedRankedLayerProof
import LogicLineages.StandardControlCurrent.PolicyIndexedRankedGraphProof
import LogicLineages.StandardControlCurrent.PolicyIndexedMergeProof
import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedPartial
open OrdinalComparison Source Source.OrdinalSyntax
open Nat.Partrec (Code)

private theorem levelPrim : Primrec (Prod.fst : Node → Nat) := Primrec.fst
private theorem iPrim : Primrec (fun p : Node => p.2.1) := Primrec.fst.comp Primrec.snd
private theorem rankPrim : Primrec rank := Primrec.snd.comp Primrec.snd
private theorem tagPrim : Primrec (fun p : Node => p.2.2%8) :=
  Primrec.nat_mod.comp rankPrim (Primrec.const 8)
private theorem headPrim : Primrec (fun p : Node => (p.2.2/8).unpair) :=
  Primrec.unpair.comp (Primrec.nat_div.comp rankPrim (Primrec.const 8))
private theorem tagIs (k : Nat) : PrimrecPred (fun p : Node => p.2.2%8=k) :=
  Primrec.eq.comp tagPrim (Primrec.const k)
private theorem activePrim : PrimrecPred (fun p : Node => active p.2.2) :=
  (tagIs 4).or ((tagIs 5).or (tagIs 6))

private theorem childrenPrim : Primrec children :=
  Primrec.ite activePrim
    (Primrec.list_cons.comp
      (levelPrim.pair ((Primrec.ite (tagIs 4) iPrim (Primrec.ite (tagIs 5)
        (Primrec.succ.comp iPrim) (Primrec.const 1))).pair (Primrec.fst.comp headPrim)))
      (Primrec.list_cons.comp
        (levelPrim.pair ((Primrec.ite (tagIs 6) (Primrec.const 0) iPrim).pair
          (Primrec.snd.comp headPrim))) (Primrec.const []))) (Primrec.const [])

private theorem nodePrim {α : Type} [Primcodable α] {t a b : α → Nat}
    (ht : Primrec t) (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => node (t x) (a x) (b x)) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
    (Primrec₂.natPair.comp ha hb)) ht

private theorem freePrim : Primrec (fun s : Node => partialFree s.1 s.2.1 s.2.2) := by
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp levelPrim (Primrec.const 2)))
  exact Primrec.ite (Primrec.eq.comp (iPrim.comp Primrec.fst) Primrec.snd)
    (nodePrim (Primrec.const 4)
      (ordinalSyntaxHeadOperationsPrimitiveRecursive.2.1.comp (rankPrim.comp Primrec.fst))
      (Primrec.const 1)) (Primrec.const 1)

private theorem replicatePrim : Primrec (fun s : Node => List.replicate (s.1+2) 1) := by
  have h := Primrec.list_map (Primrec.list_range.comp
    (Primrec.nat_add.comp levelPrim (Primrec.const 2))) (Primrec.const 1).to₂
  exact h.of_eq (fun s => by simp)

private theorem collapseVectorPrim {α : Type} [Primcodable α] {l head : α → Nat} {a b : α → List Nat}
    (hl : Primrec l) (hh : Primrec head) (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => partialCollapse (l x) (head x) (a x) (b x)) := by
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp hl (Primrec.const 2)))
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (nodePrim (Primrec.const 6)
      (ordinalSyntaxHeadOperationsPrimitiveRecursive.2.1.comp (hh.comp Primrec.fst))
      ((Primrec.list_getD 0).comp (hb.comp Primrec.fst) (Primrec.const 0)))
    (nodePrim (Primrec.const 4)
      ((Primrec.list_getD 0).comp (ha.comp Primrec.fst) Primrec.snd)
      ((Primrec.list_getD 0).comp (hb.comp Primrec.fst) Primrec.snd))

private theorem childPairComputable : Computable childPair := by
  have pick (k : Nat) : Computable (fun xs : List Value => xs.getD k none) :=
    (Primrec.list_getD (none : Value)).to_comp.comp Computable.id (Computable.const k)
  let T := List Value × List Nat
  have f : Computable (fun x : T => x.1.getD 1 none) := (pick 1).comp Computable.fst
  have k : Computable₂ (fun (x : T) (b : List Nat) => (x.2,b)) :=
    ((Computable.snd.comp Computable.fst).pair Computable.snd).to₂
  exact Computable.option_bind (pick 0) (Computable.option_map f k).to₂

private theorem collapseComputable : Computable₂ collapse := by
  have get : Computable (fun p : Args => childPair p.2) := childPairComputable.comp Computable.snd
  let X := Args × (List Nat × List Nat)
  have s : Primrec (fun x : X => x.1.1) := Primrec.fst.comp Primrec.fst
  have applied : Primrec (fun x : X => partialCollapse x.1.1.1
      (x.1.1.2.2/8).unpair.1 x.2.1 x.2.2) :=
    collapseVectorPrim (levelPrim.comp s) ((Primrec.fst.comp headPrim).comp s)
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact (Computable.option_map get applied.to₂.to_comp).to₂

private theorem choose {T Y : Type} [Primcodable T] [Primcodable Y]
    {guard : T → Prop} [DecidablePred guard] {yes no : T → Part Y}
    (hg : PrimrecPred guard) (hy : Partrec yes) (hn : Partrec no) :
    Partrec (fun x => if guard x then yes x else no x) :=
  (Partrec.cond hg.decide.to_comp hy hn).of_eq (by intro x; by_cases e : guard x <;> simp [e])

private theorem runMergePartrec : Partrec (fun p : Code × Nat × Nat × List Value =>
    indexedMerge p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let T := Code × Nat × Nat × List Value
  let U := T × (List Nat × List Nat)
  have xs : Computable (fun p : T => p.2.2.2) := Computable.snd.comp
    (Computable.snd.comp Computable.snd)
  have opt : Computable (fun p : T => childPair p.2.2.2) := childPairComputable.comp xs
  have key : Computable (fun p : U => p.1.1) := Computable.fst.comp Computable.fst
  have tail : Computable (fun p : U => p.1.2) := Computable.snd.comp Computable.fst
  have level : Computable (fun p : U => p.1.2.1) := Computable.fst.comp tail
  have tag : Computable (fun p : U => p.1.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp tail)
  have go : Partrec₂ (fun (p : T) (ab : List Nat × List Nat) =>
      PolicyIndexedMerge.merge (p.1,p.2.1,p.2.2.1,ab.1,ab.2)) :=
    (PolicyIndexedMerge.mergePartrec.comp (key.pair (level.pair (tag.pair Computable.snd)))).to₂
  have call := Partrec.bind (Computable.ofOption opt) go
  have flag := Primrec.option_isSome.to_comp.comp opt
  apply (Partrec.cond flag call (Partrec.const' (Part.some (none : Value)))).of_eq
  intro p
  cases e : childPair p.2.2.2 <;> simp [indexedMerge,e,Part.bind_some]

private theorem dispatchPartrec {T : Type} [Primcodable T] {s : T → Node} {xs : T → List Value}
    {join : Nat → T → Part Value}
    (hs : Primrec s) (hx : Computable xs) (hj : ∀ k : Nat, Partrec (join k))
    :
    Partrec (fun x => caseBody Part.some (fun _ k _ => join k x) (s x) (xs x)) := by
  have split (k : Nat) : PrimrecPred (fun x => (s x).2.2%8=k) := (tagIs k).comp hs
  have isActive : PrimrecPred (fun x => active (s x).2.2) := activePrim.comp hs
  have i : Primrec (fun x => (s x).2.1) := iPrim.comp hs
  have hFree : PrimrecPred (fun x => headFree (s x).2.2 = true) :=
    Primrec.eq.comp (ordinalSyntaxHeadOperationsPrimitiveRecursive.1.comp (rankPrim.comp hs))
      (Primrec.const true)
  have matches : PrimrecPred (fun x => (s x).2.1 = ((s x).2.2/8).unpair.2) :=
    Primrec.eq.comp i ((Primrec.snd.comp headPrim).comp hs)
  have positive : PrimrecPred (fun x => 0 < (s x).2.1) := Primrec.nat_lt.comp (Primrec.const 0) i
  have zero : PrimrecPred (fun x => (s x).2.1=0) := Primrec.eq.comp i (Primrec.const 0)
  have fstCase : Partrec (fun x => Part.some (some (partialFree (s x).1 (s x).2.1 (s x).2.2))) :=
    (Computable.option_some.comp (freePrim.to_comp.comp hs.to_comp)).partrec
  have repCase : Partrec (fun x => Part.some (some (List.replicate ((s x).1+2) 1))) :=
    (Computable.option_some.comp (replicatePrim.to_comp.comp hs.to_comp)).partrec
  have collapseCase : Partrec (fun x => Part.some (collapse (s x) (xs x))) :=
    (collapseComputable.comp hs.to_comp hx).partrec
  have empty : Partrec (fun _ : T => Part.some (none : Value)) := Partrec.const' _
  exact choose hFree fstCase (choose (split 3) (choose matches repCase empty)
    (choose isActive (choose (split 4) (hj 4)
      (choose (split 5) (choose positive (hj 5) empty) (choose zero collapseCase empty))) empty))

theorem assemblePartrec : Partrec₂ assemble := by
  let T := Code × Args
  have key : Computable (Prod.fst : T → Code) := Computable.fst
  have s : Primrec (fun p : T => p.2.1) := Primrec.fst.comp Primrec.snd
  have xs : Computable (fun p : T => p.2.2) := Computable.snd.comp Computable.snd
  have level : Computable (fun p : T => p.2.1.1) := levelPrim.to_comp.comp s.to_comp
  have join (k : Nat) : Partrec (fun p : T => indexedMerge p.1 p.2.1.1 k p.2.2) :=
    runMergePartrec.comp (key.pair (level.pair ((Computable.const k).pair xs)))
  have body := dispatchPartrec s xs join
  have finish : Computable₂ (fun (_ : T) (v : Value) => some v) :=
    (Computable.option_some.comp Computable.snd).to₂
  exact (Partrec.map body finish).to₂

theorem indexedPartialRunPartrec : Partrec run := by
  have layer := PolicyIndexedRankedLayer.indexedLayerEffectivity _ _ _ children assemble
    childrenPrim assemblePartrec
  exact (PolicyIndexedRankedGraph.policyIndexedRankedEffectivity _ _ _ rank children
    (PolicyIndexedRankedLayer.layer children assemble) rankPrim childrenPrim layer).2

end LogicLineages.StandardControlCurrent.PolicyIndexedPartial
