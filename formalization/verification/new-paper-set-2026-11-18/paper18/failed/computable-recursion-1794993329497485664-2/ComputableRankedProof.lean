/-
Finite graph construction adapted from Mathlib.Computability.Primrec.List,
Copyright (c) 2018 Mario Carneiro, Apache 2.0. The assembly computation here
is merely Computable; no primitive-recursive selector assumption is made.
-/
module
public import LogicLineages.StandardControlCurrent.ComputableFoldProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.ComputableRankedProof
open ComputableFoldProof

theorem ranked : ComputableRecursionTargets.RankedRecursion := by
  intro β σ _ _ f m l g hm hl hg Ord H
  letI : DecidableEq β := Encodable.decidableEqOfEncodable β
  let mapGraph (M : List (β × σ)) (bs : List β) : List σ := bs.flatMap (Option.toList <| M.lookup ·)
  let bindList (b : β) : Nat → List β := fun n => n.rec [b] fun _ bs => bs.flatMap l
  let graph (b : β) : Nat → List (β × σ) := fun i => i.rec [] fun i ih =>
    (bindList b (m b - i)).filterMap fun b' => (g b' <| mapGraph ih (l b')).map (b', ·)
  have mapGraph_primrec : Primrec₂ mapGraph :=
    Primrec.to₂ <| Primrec.list_flatMap Primrec.snd <| Primrec.optionToList.comp₂ <|
      Primrec.listLookup.comp₂ .right (Primrec.fst.comp₂ .left)
  have bindList_primrec : Primrec₂ bindList :=
    Primrec.nat_rec' Primrec.snd
      (Primrec.list_cons.comp Primrec.fst (Primrec.const []))
      (Primrec.to₂ <| Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) (hl.comp₂ .right))
  have graph_computable : Computable (fun p : β × Nat => graph p.1 p.2) := by
    have hfront : Computable (fun p : (β × Nat) × Nat × List (β × σ) =>
        bindList p.1.1 (m p.1.1 - p.2.1)) :=
      bindList_primrec.to_comp.comp (Computable.fst.comp Computable.fst)
        (Primrec.nat_sub.to_comp.comp (hm.to_comp.comp (Computable.fst.comp Computable.fst))
          (Computable.fst.comp Computable.snd))
    have hasm : Computable (fun p : ((β × Nat) × Nat × List (β × σ)) × β =>
        (g p.2 (mapGraph p.1.2.2 (l p.2))).map (p.2, ·)) := by
      have hv : Computable (fun p : ((β × Nat) × Nat × List (β × σ)) × β =>
          g p.2 (mapGraph p.1.2.2 (l p.2))) :=
        Computable.comp (f := fun q : β × List σ => g q.1 q.2)
          (g := fun p : ((β × Nat) × Nat × List (β × σ)) × β =>
            (p.2, mapGraph p.1.2.2 (l p.2))) hg
          (Computable.snd.pair
            (mapGraph_primrec.to_comp.comp
              (Computable.snd.comp (Computable.snd.comp Computable.fst))
              (hl.to_comp.comp Computable.snd)))
      exact Computable.option_map hv
        ((Computable.snd.comp Computable.fst).pair Computable.snd).to₂
    exact Computable.nat_rec Computable.snd (Computable.const [])
      (filterMapProgram hfront hasm).to₂
  have hc : Computable (fun b => (graph b (m b + 1))[0]?.map Prod.snd) :=
    Computable.option_map
      (Primrec.list_getElem?.to_comp.comp
        (graph_computable.comp (Computable.id.pair (Computable.succ.comp hm.to_comp)))
        (Computable.const 0))
      (Computable.snd.comp Computable.snd).to₂
  exact Computable.option_some_iff.mp <| hc.of_eq <| fun b => by
    have graph_eq_map_bindList (i : ℕ) (hi : i ≤ m b + 1) :
        graph b i = (bindList b (m b + 1 - i)).map fun x ↦ (x, f x) := by
      have bindList_eq_nil : bindList b (m b + 1) = [] :=
        have bindList_m_lt (k : ℕ) : ∀ b' ∈ bindList b k, m b' < m b + 1 - k := by
          induction k with simp [bindList]
          | succ k ih =>
            grind
        List.eq_nil_iff_forall_not_mem.mpr
          (by intro b' ha'; by_contra; simpa using bindList_m_lt (m b + 1) b' ha')
      have mapGraph_graph {bs bs' : List β} (has : bs' ⊆ bs) :
          mapGraph (bs.map <| fun x => (x, f x)) bs' = bs'.map f := by
        induction bs' with simp [mapGraph]
        | cons b bs' ih =>
          have : b ∈ bs ∧ bs' ⊆ bs := by simpa using has
          rcases this with ⟨ha, has'⟩
          simpa [List.lookup_graph f ha] using ih has'
      have graph_succ : ∀ i, graph b (i + 1) =
        (bindList b (m b - i)).filterMap fun b' =>
          (g b' <| mapGraph (graph b i) (l b')).map (b', ·) := fun _ => rfl
      have bindList_succ : ∀ i, bindList b (i + 1) = (bindList b i).flatMap l := fun _ => rfl
      induction i with
      | zero => symm; simpa [graph] using bindList_eq_nil
      | succ i ih =>
        simp only [graph_succ, ih (Nat.le_of_lt hi), Nat.succ_sub (Nat.le_of_lt_succ hi),
          Nat.succ_eq_add_one, bindList_succ, Nat.reduceSubDiff]
        apply List.filterMap_eq_map_iff_forall_eq_some.mpr
        intro b' ha'; simp; rw [mapGraph_graph]
        · exact H b'
        · exact (List.infix_flatMap_of_mem ha' l).subset
    simp [graph_eq_map_bindList (m b + 1) (Nat.le_refl _), bindList]

end LogicLineages.StandardControlCurrent.ComputableRankedProof
