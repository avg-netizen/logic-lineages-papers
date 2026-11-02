module
public import LogicLineages.OrdinalComparison.UnitEliminationTreeCodeTargets
public import Mathlib.Computability.Partrec
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitEliminationTreeCode.Proof
attribute [local irreducible] Nat.sqrt Nat.unpair

private def step (leaf : Nat→Nat) (free : Nat→Nat→Nat) (active : Nat→Nat→Nat→Nat)
    (xs : List Nat) : Nat :=
  let p := (xs.length/4).unpair
  if xs.length%4=1 then free p.1 (xs.getD p.2 0)
  else if xs.length%4=2 then active p.1 (xs.getD p.2.unpair.1 0) (xs.getD p.2.unpair.2 0)
  else leaf (xs.length/4)

private theorem step_exact (leaf : Nat→Nat) (free : Nat→Nat→Nat) (active : Nat→Nat→Nat→Nat) (n : Nat) :
    step leaf free active ((List.range n).map (fold leaf free active))=fold leaf free active n := by
  conv_rhs => rw [fold]
  simp only [step,List.length_map,List.length_range]
  by_cases h : n%4=1 ∨ n%4=2
  · have hd : n/4<n := Nat.div_lt_self (by omega) (by decide)
    have hc : (n/4).unpair.2<n := (Nat.unpair_right_le _).trans_lt hd
    have hl : (n/4).unpair.2.unpair.1<n := (Nat.unpair_left_le _).trans_lt hc
    have hr : (n/4).unpair.2.unpair.2<n := (Nat.unpair_right_le _).trans_lt hc
    simp only [if_pos h,List.getD_eq_getElem?_getD,List.getElem?_map,
      List.getElem?_range hc,List.getElem?_range hl,List.getElem?_range hr,Option.map_some,Option.getD_some]
    rcases h with h1|h2
    · simp [h1]
    · have h1 : n%4≠1 := by omega
      simp [h1,h2]
  · have h1 : n%4≠1 := fun h1=>h (Or.inl h1)
    have h2 : n%4≠2 := fun h2=>h (Or.inr h2)
    simp only [dif_neg h,if_neg h1,if_neg h2]

private theorem step_primitive (leaf : Nat→Nat) (free : Nat→Nat→Nat) (active : Nat→Nat→Nat→Nat)
    (hlf : Primrec leaf) (hfr : Primrec₂ free)
    (hac : Primrec (fun p : Nat×Nat×Nat => active p.1 p.2.1 p.2.2)) : Primrec (step leaf free active) := by
  have hn : Primrec (fun xs : List Nat=>xs.length) := Primrec.list_length
  have hm := Primrec.nat_mod.comp hn (Primrec.const 4)
  have hd := Primrec.nat_div.comp hn (Primrec.const 4)
  have hp := Primrec.unpair.comp hd
  have hmeta := Primrec.fst.comp hp
  have hchild := Primrec.snd.comp hp
  have hleft := Primrec.fst.comp (Primrec.unpair.comp hchild)
  have hright := Primrec.snd.comp (Primrec.unpair.comp hchild)
  have hv := (Primrec.list_getD (0 : Nat)).comp Primrec.id hchild
  have hvl := (Primrec.list_getD (0 : Nat)).comp Primrec.id hleft
  have hvr := (Primrec.list_getD (0 : Nat)).comp Primrec.id hright
  exact Primrec.ite (Primrec.eq.comp hm (Primrec.const 1)) (hfr.comp hmeta hv)
    (Primrec.ite (Primrec.eq.comp hm (Primrec.const 2)) (hac.comp (hmeta.pair (hvl.pair hvr))) (hlf.comp hd))

private theorem ite_computable {α β : Type} [Primcodable α] [Primcodable β]
    {p : α→Prop} [DecidablePred p] {f g : α→β}
    (hp : PrimrecPred p) (hf : Computable f) (hg : Computable g) :
    Computable (fun a=>if p a then f a else g a) := by
  simpa only [Bool.cond_decide] using Computable.cond hp.decide.to_comp hf hg

private theorem step_computable (leaf : Nat→Nat) (free : Nat→Nat→Nat) (active : Nat→Nat→Nat→Nat)
    (hlf : Computable leaf) (hfr : Computable₂ free)
    (hac : Computable (fun p : Nat×Nat×Nat => active p.1 p.2.1 p.2.2)) : Computable (step leaf free active) := by
  have hn : Primrec (fun xs : List Nat=>xs.length) := Primrec.list_length
  have hm := Primrec.nat_mod.comp hn (Primrec.const 4)
  have hd := Primrec.nat_div.comp hn (Primrec.const 4)
  have hp := Primrec.unpair.comp hd
  have hmeta := Primrec.fst.comp hp
  have hchild := Primrec.snd.comp hp
  have hleft := Primrec.fst.comp (Primrec.unpair.comp hchild)
  have hright := Primrec.snd.comp (Primrec.unpair.comp hchild)
  have hv := (Primrec.list_getD (0 : Nat)).comp Primrec.id hchild
  have hvl := (Primrec.list_getD (0 : Nat)).comp Primrec.id hleft
  have hvr := (Primrec.list_getD (0 : Nat)).comp Primrec.id hright
  exact ite_computable (Primrec.eq.comp hm (Primrec.const 1)) (hfr.comp hmeta.to_comp hv.to_comp)
    (ite_computable (Primrec.eq.comp hm (Primrec.const 2))
      (hac.comp (hmeta.pair (hvl.pair hvr)).to_comp) (hlf.comp hd.to_comp))

 theorem fold_primitive (leaf : Nat→Nat) (free : Nat→Nat→Nat) (active : Nat→Nat→Nat→Nat)
    (hlf : Primrec leaf) (hfr : Primrec₂ free)
    (hac : Primrec (fun p : Nat×Nat×Nat => active p.1 p.2.1 p.2.2)) : Primrec (fold leaf free active) := by
  have h : Primrec₂ (fun (_ : Unit) n=>fold leaf free active n) :=
    Primrec.nat_strong_rec _
      (Primrec.option_some.comp ((step_primitive leaf free active hlf hfr hac).comp Primrec.snd)).to₂
      (fun _ n=>congrArg Option.some (step_exact leaf free active n))
  exact h.comp (Primrec.const ()) Primrec.id

 theorem fold_computable (leaf : Nat→Nat) (free : Nat→Nat→Nat) (active : Nat→Nat→Nat→Nat)
    (hlf : Computable leaf) (hfr : Computable₂ free)
    (hac : Computable (fun p : Nat×Nat×Nat => active p.1 p.2.1 p.2.2)) : Computable (fold leaf free active) := by
  have h : Computable₂ (fun (_ : Unit) n=>fold leaf free active n) :=
    Computable.nat_strong_rec _
      (Computable.option_some.comp ((step_computable leaf free active hlf hfr hac).comp Computable.snd)).to₂
      (fun _ n=>congrArg Option.some (step_exact leaf free active n))
  exact h.comp (Computable.const ()) Computable.id

 theorem effectiveConstructorsAndFold : Targets.EffectiveConstructorsAndFold := by
  refine ⟨?_,?_,?_,fold_primitive,fold_computable⟩
  · exact Primrec.nat_mul.comp (Primrec.const 4) Primrec.id
  · exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) Primrec₂.natPair) (Primrec.const 1)
  · have hm : Primrec (fun p : Nat×Nat×Nat=>p.1) := Primrec.fst
    have hl : Primrec (fun p : Nat×Nat×Nat=>p.2.1) := Primrec.fst.comp Primrec.snd
    have hr : Primrec (fun p : Nat×Nat×Nat=>p.2.2) := Primrec.snd.comp Primrec.snd
    exact Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp hm (Primrec₂.natPair.comp hl hr)))
      (Primrec.const 2)
end LogicLineages.OrdinalComparison.Source.UnitEliminationTreeCode.Proof
