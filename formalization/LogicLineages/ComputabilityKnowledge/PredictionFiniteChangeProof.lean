module

public import LogicLineages.ComputabilityKnowledge.PredictionFiniteChangeTargets
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionFiniteChangeProof
open PredictionFiniteChange PredictionFiniteChangeTargets

private theorem passes_iff (R : Matrix) (z k s t : Nat) :
    passes R z k s t = true ↔ ∀ u : Nat, u ≤ t → R (z, k, s, u) = true := by
  simp only [passes, List.all_eq_true, List.mem_range]
  constructor <;> intro h u hu <;> exact h u (by omega)

private theorem candidate_le (R : Matrix) (z k s t : Nat) (hs : s ≤ t)
    (hp : passes R z k s t = true) : candidate R z k t ≤ s := by
  by_contra hn
  have hfalse := List.not_of_lt_findIdx (xs := List.range (t + 1))
    (p := fun a => passes R z k a t) (by change s < candidate R z k t; omega)
  have hf : passes R z k s t = false := by simpa using hfalse
  rw [hp] at hf
  contradiction

theorem candidateSpecification : CandidateSpecification := by
  intro R z k t
  have hbound : candidate R z k t ≤ t + 1 := by
    simpa only [candidate, List.length_range] using
      List.findIdx_le_length (p := fun s => passes R z k s t) (xs := List.range (t + 1))
  refine ⟨hbound, ?_, ?_⟩
  · intro hc
    have hsel := List.findIdx_getElem (xs := List.range (t + 1))
      (p := fun s => passes R z k s t) (w := by simpa only [candidate, List.length_range] using (show candidate R z k t < t + 1 by omega))
    have hp : passes R z k (candidate R z k t) t = true := by simpa only [List.getElem_range, candidate] using hsel
    exact (passes_iff R z k _ t).mp hp
  · intro s hs hst
    have hfalse := List.not_of_lt_findIdx (xs := List.range (t + 1))
      (p := fun a => passes R z k a t) hs
    have hf : passes R z k s t = false := by simpa using hfalse
    by_contra hnone
    have hp : passes R z k s t = true := (passes_iff R z k s t).mpr (by
      intro u hu
      cases he : R (z, k, s, u) with
      | false => exact False.elim (hnone ⟨u, hu, he⟩)
      | true => rfl)
    rw [hp] at hf
    contradiction

private theorem bad_prefix (R : Matrix) (z k b : Nat)
    (hbad : ∀ s : Nat, s < b → ¬ ∀ u : Nat, R (z, k, s, u) = true) :
    ∃ T : Nat, b ≤ T ∧ ∀ s : Nat, s < b → ∃ u : Nat, u ≤ T ∧ R (z, k, s, u) = false := by
  classical
  induction b with
  | zero => exact ⟨0, le_rfl, fun s hs => False.elim (by omega)⟩
  | succ b ih =>
    obtain ⟨T, hT, hprefix⟩ := ih (fun s hs => hbad s (by omega))
    have hb := hbad b (by omega)
    push_neg at hb
    obtain ⟨u, hu⟩ := hb
    have huf : R (z, k, b, u) = false := by cases he : R (z, k, b, u) <;> simp_all
    refine ⟨max (max T u) (b + 1), Nat.le_max_right _ _, ?_⟩
    intro s hs
    by_cases heq : s = b
    · subst s
      exact ⟨u, (Nat.le_max_right T u).trans (Nat.le_max_left _ _), huf⟩
    · obtain ⟨v, hv, hval⟩ := hprefix s (by omega)
      exact ⟨v, hv.trans ((Nat.le_max_left T u).trans (Nat.le_max_left _ _)), hval⟩

theorem leastWitnessStabilization : LeastWitnessStabilization := by
  intro R z k s hs hmin
  obtain ⟨T, hsT, hbad⟩ := bad_prefix R z k s hmin
  refine ⟨T, ?_⟩
  intro t ht
  have hle := candidate_le R z k s t (by omega) ((passes_iff R z k s t).mpr (fun u _ => hs u))
  by_contra hne
  have hlt : candidate R z k t < s := by omega
  obtain ⟨u, hu, hfalse⟩ := hbad _ hlt
  have htrue := (candidateSpecification R z k t).2.1 (by omega) u (by omega)
  rw [htrue] at hfalse
  contradiction

theorem noWitnessEscape : NoWitnessEscape := by
  intro R z k hnone b
  obtain ⟨T, hbT, hbad⟩ := bad_prefix R z k (b + 1) (fun s _ hs => hnone ⟨s, hs⟩)
  refine ⟨T, ?_⟩
  intro t ht
  by_contra hn
  obtain ⟨u, hu, hfalse⟩ := hbad (candidate R z k t) (by omega)
  have htrue := (candidateSpecification R z k t).2.1 (by omega) u (by omega)
  rw [htrue] at hfalse
  contradiction

private theorem event_iff (R : Matrix) (z k t : Nat) :
    changeEvent R z k t = true ↔ 0 < t ∧ candidate R z k t ≠ candidate R z k (t - 1) := by
  simp [changeEvent]

theorem finiteChangesIffWitness : FiniteChangesIffWitness := by
  classical
  intro R z k
  constructor
  · intro hfin
    let N := hfin.toFinset.sup id
    have hbound : ∀ t : Nat, t ∈ changeSet R z k → t ≤ N := by
      intro t ht
      exact Finset.le_sup (f := id) (hfin.mem_toFinset.mpr ht)
    have hstep : ∀ t : Nat, N < t → candidate R z k t = candidate R z k (t - 1) := by
      intro t ht
      by_contra hn
      have hmem : t ∈ changeSet R z k := (event_iff R z k t).mpr ⟨by omega, hn⟩
      have := hbound t hmem
      omega
    have hstable : ∀ t : Nat, N ≤ t → candidate R z k t = candidate R z k N := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => rfl
      | succ t ht ih =>
        rw [hstep (t + 1) (by omega)]
        simpa only [Nat.add_sub_cancel] using ih
    refine ⟨candidate R z k N, ?_⟩
    intro u
    let t := max (max N u) (candidate R z k N)
    have hNt : N ≤ t := (Nat.le_max_left N u).trans (Nat.le_max_left _ _)
    have hut : u ≤ t := (Nat.le_max_right N u).trans (Nat.le_max_left _ _)
    have hs := hstable t hNt
    have hv := (candidateSpecification R z k t).2.1
      (by rw [hs]; exact Nat.le_max_right _ _) u hut
    simpa only [hs] using hv
  · intro hex
    let s := Nat.find hex
    have hs : ∀ u : Nat, R (z, k, s, u) = true := Nat.find_spec hex
    have hmin : ∀ r : Nat, r < s → ¬ ∀ u : Nat, R (z, k, r, u) = true := by
      intro r hr
      exact Nat.find_min hex hr
    obtain ⟨T, hT⟩ := leastWitnessStabilization R z k s hs hmin
    apply (Finset.range (T + 1)).finite_toSet.subset
    intro t ht
    simp only [Finset.mem_coe, Finset.mem_range]
    have he := (event_iff R z k t).mp ht
    by_contra hn
    have ha := hT t (by omega)
    have hb := hT (t - 1) (by omega)
    exact he.2 (ha.trans hb.symm)

private theorem computable_range_map {α β : Type} [Primcodable α] [Primcodable β]
    {f : α → Nat → β} (hf : Computable₂ f) :
    Computable (fun q : α × Nat => (List.range q.2).map (f q.1)) := by
  have hstep : Computable₂ (fun q : α × Nat => fun v : Nat × List β =>
      v.2 ++ [f q.1 v.1]) :=
    (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))).to₂
  apply (Computable.nat_rec Computable.snd (Computable.const []) hstep).of_eq
  intro q
  induction q.2 with
  | zero => rfl
  | succ n ih => simp only [Nat.rec_add_one, ih, List.range_succ, List.map_append, List.map_singleton]

private theorem pr_all_bits : Primrec (fun l : List Bool => l.all id) := by
  have h := Primrec.list_foldr (Primrec.id : Primrec (fun l : List Bool => l)) (Primrec.const true)
    ((Primrec.and.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)
  apply h.of_eq
  intro l
  change l.foldr (fun b s => b && s) true = l.all id
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, List.all_cons, id_eq, ih]

private theorem comp_passes (R : Matrix) (hR : Computable R) :
    Computable (fun q : Nat × Nat × Nat × Nat => passes R q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  have hval : Computable₂ (fun p : Nat × Nat × Nat => fun u : Nat => R (p.1, p.2.1, p.2.2, u)) :=
    (hR.comp ((Computable.fst.comp Computable.fst).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair Computable.snd)))).to₂
  have hm := computable_range_map hval
  have harg : Computable (fun q : Nat × Nat × Nat × Nat =>
      ((q.1, q.2.1, q.2.2.1), q.2.2.2 + 1)) :=
    ((Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      (Computable.fst.comp (Computable.snd.comp Computable.snd)))).pair
      (Computable.succ.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))))
  apply (pr_all_bits.to_comp.comp (hm.comp harg)).of_eq
  intro q
  simp only [passes, List.all_map, Function.comp_def, id_eq]

private theorem comp_candidate (R : Matrix) (hR : Computable R) :
    Computable (fun q : Nat × Nat × Nat => candidate R q.1 q.2.1 q.2.2) := by
  have hp : Computable₂ (fun p : Nat × Nat × Nat => fun s : Nat => passes R p.1 p.2.1 s p.2.2) :=
    ((comp_passes R hR).comp ((Computable.fst.comp Computable.fst).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        (Computable.snd.pair (Computable.snd.comp (Computable.snd.comp Computable.fst)))))).to₂
  have hm := computable_range_map hp
  have ha : Computable (fun q : Nat × Nat × Nat => (q, q.2.2 + 1)) :=
    Computable.id.pair (Computable.succ.comp (Computable.snd.comp Computable.snd))
  have hfind : Primrec (fun l : List Bool => l.findIdx id) :=
    Primrec.list_findIdx Primrec.id Primrec.snd.to₂
  apply (hfind.to_comp.comp (hm.comp ha)).of_eq
  intro q
  change ((List.range (q.2.2 + 1)).map (fun s => passes R q.1 q.2.1 s q.2.2)).findIdx id = _
  unfold candidate
  induction List.range (q.2.2 + 1) with
  | nil => rfl
  | cons s l ih => simp [List.findIdx_cons, ih]

private theorem pr_positive_stage : Primrec (fun q : Nat × Nat × Nat => decide (0 < q.2.2)) := by
  have h : PrimrecPred (fun q : Nat × Nat × Nat => 0 < q.2.2) :=
    Primrec.nat_lt.comp (Primrec.const 0) (Primrec.snd.comp Primrec.snd)
  exact h.decide

private theorem pr_unequal : Primrec (fun p : Nat × Nat => decide (p.1 ≠ p.2)) := by
  have h : PrimrecPred (fun p : Nat × Nat => p.1 = p.2) :=
    Primrec.eq.comp Primrec.fst Primrec.snd
  exact h.not.decide

private theorem comp_previous (R : Matrix) (hR : Computable R) :
    Computable (fun q : Nat × Nat × Nat => candidate R q.1 q.2.1 (q.2.2 - 1)) := by
  have ha : Computable (fun q : Nat × Nat × Nat => (q.1, q.2.1, q.2.2 - 1)) :=
    Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      (Primrec.nat_sub.to_comp.comp (Computable.snd.comp Computable.snd) (Computable.const 1)))
  apply ((comp_candidate R hR).comp ha).of_eq
  intro q
  dsimp only

private theorem comp_changed (R : Matrix) (hR : Computable R) :
    Computable (fun q : Nat × Nat × Nat => decide (candidate R q.1 q.2.1 q.2.2 ≠ candidate R q.1 q.2.1 (q.2.2 - 1))) := by
  apply (pr_unequal.to_comp.comp ((comp_candidate R hR).pair (comp_previous R hR))).of_eq
  intro q
  dsimp only

theorem finiteChangeComputable : FiniteChangeComputable := by
  intro R hR
  refine ⟨comp_candidate R hR, ?_⟩
  have h : Computable (fun q : Nat × Nat × Nat =>
      decide (0 < q.2.2) && decide (candidate R q.1 q.2.1 q.2.2 ≠ candidate R q.1 q.2.1 (q.2.2 - 1))) :=
    Primrec.and.to_comp.comp pr_positive_stage.to_comp (comp_changed R hR)
  apply h.of_eq
  intro q
  change _ = changeEvent R q.1 q.2.1 q.2.2
  unfold changeEvent
  rfl

theorem finiteChangeCharacteristicProgram : FiniteChangeCharacteristicProgram := by
  intro R hR
  have he := (finiteChangeComputable R hR).2
  have harg : Computable (fun n : Nat => (n.unpair.1, n.unpair.2.unpair.1, n.unpair.2.unpair.2)) :=
    (Computable.fst.comp Computable.unpair).pair
      (((Computable.fst.comp Computable.unpair).comp (Computable.snd.comp Computable.unpair)).pair
        ((Computable.snd.comp Computable.unpair).comp (Computable.snd.comp Computable.unpair)))
  have hu : Computable (fun n : Nat => changeEvent R n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2) := by
    apply (he.comp harg).of_eq
    intro n
    dsimp only
  have hb : Primrec (fun b : Bool => if b then (1 : Nat) else 0) :=
    (Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)).of_eq (fun b => by cases b <;> rfl)
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp (hb.to_comp.comp hu).partrec)
  refine ⟨p, ?_⟩
  intro z k t
  rw [hp]
  change Part.some (if changeEvent R (Nat.pair z (Nat.pair k t)).unpair.1
    (Nat.pair z (Nat.pair k t)).unpair.2.unpair.1
    (Nat.pair z (Nat.pair k t)).unpair.2.unpair.2 then 1 else 0) = _
  simp only [Nat.unpair_pair]

theorem freshStageEnumeration : FreshStageEnumeration := by
  intro R z k
  refine ⟨by simp [stageOutput, changeEvent], ?_, ?_⟩
  · intro t a
    cases he : changeEvent R z k t with
    | false => simp [stageOutput, changeSet, he]
    | true =>
      simp only [stageOutput, changeSet, Set.mem_setOf_eq, he, ↓reduceIte, Option.some.injEq, and_true]
      exact eq_comm
  · intro s t hst h
    cases he : changeEvent R z k s <;> simp [stageOutput, he] at h
    omega

theorem piThreeFiniteChangeReduction : PiThreeFiniteChangeReduction := by
  intro R z
  exact forall_congr' (fun k => (finiteChangesIffWitness R z k).symm)

end LogicLineages.ComputabilityKnowledge.PredictionFiniteChangeProof
