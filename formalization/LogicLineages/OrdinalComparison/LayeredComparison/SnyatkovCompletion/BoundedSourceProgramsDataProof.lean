module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsGraphProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsProof
open BoundedSourcePrograms ScopedPhiProgramsGraph
attribute [local irreducible] Nat.sqrt Nat.unpair BaseTermPrograms.variablesCode

theorem update_primitive : Primrec (fun p : List Nat × (Nat × Nat) => Code.update p.1 p.2.1 p.2.2) := by
  let A := List Nat × (Nat × Nat)
  have hlen : Primrec (fun p : A => max p.1.length (p.2.1 + 1)) :=
    Primrec.nat_max.comp (Primrec.list_length.comp Primrec.fst)
      (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
  have hs : Primrec₂ (fun p : A => fun j : Nat => if j = p.2.1 then p.2.2 else p.1.getD j 0) :=
    Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact Primrec.list_map (Primrec.list_range.comp hlen) hs

theorem computable_decide_and {A : Type} [Primcodable A] {p q : A → Prop}
    [DecidablePred p] [DecidablePred q]
    (hp : Computable (fun a => decide (p a))) (hq : Computable (fun a => decide (q a))) :
    Computable (fun a => decide (p a ∧ q a)) := by
  apply (Primrec.and.to_comp.comp hp hq).of_eq
  intro a
  simp

theorem guard_computable : Computable₂ Code.guard := by
  let A := Nat × Nat
  have hc : Primrec (fun p : A => p.2) := Primrec.snd
  have hi : Primrec (fun p : A => p.1) := Primrec.fst
  have ha : Primrec (fun p : A => (p.2 / 5).unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.nat_div.comp hc (Primrec.const 5)))
  have hv : Primrec (fun p : A => (((p.2 / 5).unpair.1 / 5).unpair.1)) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.nat_div.comp ha (Primrec.const 5)))
  have hb : Primrec (fun p : A => (((p.2 / 5).unpair.1 / 5).unpair.2)) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.nat_div.comp ha (Primrec.const 5)))
  have hp0 := (Primrec.eq.comp (Primrec.nat_mod.comp hc (Primrec.const 5)) (Primrec.const 3)).decide.to_comp
  have hp1 := (Primrec.eq.comp (Primrec.nat_mod.comp ha (Primrec.const 5)) (Primrec.const 1)).decide.to_comp
  have hp2 := (Primrec.eq.comp (Primrec.nat_mod.comp hv (Primrec.const 4)) (Primrec.const 1)).decide.to_comp
  have hp3 := (Primrec.eq.comp (Primrec.nat_div.comp hv (Primrec.const 4)) hi).decide.to_comp
  have hm : PrimrecRel (fun (xs : List Nat) (i : Nat) => ∃ j ∈ xs, j = i) :=
    (show PrimrecRel (fun a b : Nat => a = b) from Primrec.eq).exists_mem_list
  have hn : PrimrecRel (fun (xs : List Nat) (i : Nat) => i ∉ xs) := hm.not.of_eq (by intros; simp)
  have hp4 : Computable (fun p : A => decide (p.1 ∉ BaseTermPrograms.variablesCode (((p.2 / 5).unpair.1 / 5).unpair.2))) :=
    hn.decide.to_comp.comp (BalancedBoxEvaluation.Base.actualComputation.2.comp hb.to_comp) hi.to_comp
  exact computable_ite (computable_decide_and hp0 (computable_decide_and hp1
    (computable_decide_and hp2 (computable_decide_and hp3 hp4))))
    (Computable.option_some.comp hb.to_comp) (Computable.const none)

/-- Ordinary finite mapping, derived from the accepted actual fold program. -/
theorem computable_map {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C] [Inhabited B]
    {xs : A → List B} {f : A → B → C} (hx : Computable xs) (hf : Computable₂ f) :
    Computable (fun a => (xs a).map (f a)) := by
  have hs : Computable₂ (fun a : A => fun p : B × List C => f a p.1 :: p.2) :=
    Computable.list_cons.comp (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  apply (BalancedBoxEvaluation.Graph.computable_foldr default hx (Computable.const []) hs).of_eq
  intro a
  induction xs a with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons, List.map_cons, ih]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsProof
