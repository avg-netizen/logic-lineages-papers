module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarNormalTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarNormal.Proof
open CotreeGrammarFlow CotreeGrammarOpen CotreeGrammarForest

variable {Q : Type} [DecidableEq Q] {δ : Q → Q → Q}

theorem realizedBalance : Targets.RealizedBalance := by
  intro Q _ _ δ root w F h q
  have hb := CotreeGrammarForest.StatementChecks.forestBalance Q δ F q
  have hr := h.2.2 q
  omega

theorem roots_perm {F G : List (Packed δ)} (h : F.Perm G) : (roots F).Perm (roots G) := h.map _

theorem holes_perm {F G : List (Packed δ)} (h : F.Perm G) : (forestHoles F).Perm (forestHoles G) :=
  List.Perm.flatMap_right _ h

theorem balanced_perm {F G : List (Packed δ)} (h : F.Perm G) {root} (hb : Balanced root F) :
    Balanced root G := by
  intro q
  rw [← (roots_perm h).count_eq, ← (holes_perm h).count_eq]
  exact hb q

theorem noCross_perm {F G : List (Packed δ)} (h : F.Perm G) (hc : NoCrossHole F) : NoCrossHole G :=
  fun a ta b tb rest hp => hc a ta b tb rest (h.trans hp)

theorem roots_count_cons (t : Packed δ) (F : List (Packed δ)) q :
    (roots (t::F)).count q = (roots F).count q + if t.1 = q then 1 else 0 := by
  by_cases h : t.1 = q <;> simp [roots,List.count_cons,beq_iff_eq,h,eq_comm]

theorem holes_count_cons (t : Packed δ) (F : List (Packed δ)) q :
    (forestHoles (t::F)).count q = (holes t.2).count q + (forestHoles F).count q := by
  simp [forestHoles,List.count_append]

theorem root_absent_of_hole (t : Packed δ) (rest : List (Packed δ))
    (hc : NoCrossHole (t::rest)) {q} (hq : q ∈ holes t.2) : q ∉ roots rest := by
  classical
  intro hm
  rcases List.mem_map.mp hm with ⟨⟨b,tb⟩,hb,he⟩
  change b = q at he
  subst b
  have hp := (List.perm_cons_erase hb).cons t
  exact hc t.1 t.2 q tb _ hp hq

theorem hole_absent_of_root (t : Packed δ) (rest : List (Packed δ))
    (hc : NoCrossHole (t::rest)) : t.1 ∉ forestHoles rest := by
  classical
  intro hm
  rcases List.mem_flatMap.mp hm with ⟨u,hu,hh⟩
  have hp := ((List.perm_cons_erase hu).cons t).trans (List.Perm.swap _ _ _)
  exact hc u.1 u.2 t.1 t.2 _ hp hh

theorem hole_local {root} (t : Packed δ) (rest : List (Packed δ))
    (hb : Balanced root (t::rest)) (hc : NoCrossHole (t::rest)) {q} (hq : q ∈ holes t.2) :
    q = t.1 ∧ q ≠ root := by
  have hz := List.count_eq_zero.mpr (root_absent_of_hole t rest hc hq)
  have hp := List.count_pos_iff.mpr hq
  have he := hb q
  rw [roots_count_cons,holes_count_cons,hz] at he
  by_cases ht : t.1 = q
  · refine ⟨ht.symm,?_⟩
    intro hr
    have hrt : root = q := hr.symm
    simp only [if_pos ht,if_pos hrt,Nat.zero_add] at he
    omega
  · simp only [if_neg ht,Nat.zero_add] at he
    omega

theorem roots_nodup {root} (F : List (Packed δ)) (hb : Balanced root F) (hc : NoCrossHole F) :
    (roots F).Nodup := by
  classical
  apply List.nodup_iff_count.mpr
  intro q
  by_cases hz : (forestHoles F).count q = 0
  · have hh := hb q
    rw [hz] at hh
    split_ifs at hh <;> omega
  · have hm : q ∈ forestHoles F := List.count_pos_iff.mp (by omega)
    rcases List.mem_flatMap.mp hm with ⟨t,ht,hq⟩
    have hp := List.perm_cons_erase ht
    have hc' := noCross_perm hp hc
    have hz' := List.count_eq_zero.mpr (root_absent_of_hole t _ hc' hq)
    rw [(roots_perm hp).count_eq,roots_count_cons,hz']
    split_ifs <;> omega

theorem component_closed {root} (t : Tree δ root) (rest : List (Packed δ))
    (hb : Balanced root (⟨root,t⟩::rest)) (hc : NoCrossHole (⟨root,t⟩::rest)) : holes t = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro q hq
  have h := hole_local ⟨root,t⟩ rest hb hc hq
  exact h.2 h.1

theorem component_cycle {root} (t : Packed δ) (rest : List (Packed δ))
    (hb : Balanced root (t::rest)) (hc : NoCrossHole (t::rest)) (hne : t.1 ≠ root) :
    holes t.2 = [t.1] := by
  have hn := roots_nodup (t::rest) hb hc
  have hnot : t.1 ∉ roots rest := (List.nodup_cons.mp hn).1
  have hz := List.count_eq_zero.mpr hnot
  have hhz := List.count_eq_zero.mpr (hole_absent_of_root t rest hc)
  have he := hb t.1
  rw [roots_count_cons,holes_count_cons,hz,hhz] at he
  simp only [if_pos rfl,if_true,if_neg (Ne.symm hne),Nat.zero_add,Nat.add_zero] at he
  have hcount : (holes t.2).count t.1 = 1 := he.symm
  have hrep := List.eq_replicate_of_mem (fun q hq => (hole_local t rest hb hc hq).1)
  have hlen : (holes t.2).length = 1 := by
    rw [hrep] at hcount
    simpa using hcount
  rw [hrep,hlen]
  rfl

theorem normalStructure : Targets.NormalStructure := by
  intro Q _ δ root F hb hc
  classical
  have hn := roots_nodup F hb hc
  have hr := hb root
  have hm : root ∈ roots F := List.count_pos_iff.mp (by simp only [if_pos rfl,if_true] at hr; omega)
  rcases List.mem_map.mp hm with ⟨⟨q,t⟩,ht,he⟩
  change q = root at he
  subst q
  let rest := F.erase ⟨root,t⟩
  have hp : F.Perm (⟨root,t⟩::rest) := List.perm_cons_erase ht
  have hb' := balanced_perm hp hb
  have hc' := noCross_perm hp hc
  have hn' := (roots_perm hp).nodup hn
  have hnot : root ∉ roots rest := (List.nodup_cons.mp hn').1
  refine ⟨t,rest,hp,component_closed t rest hb' hc',?_,hn⟩
  intro u hu
  have hne : u.1 ≠ root := by
    intro he
    apply hnot
    exact List.mem_map.mpr ⟨u,hu,he⟩
  have huF : u ∈ F := hp.mem_iff.mpr (List.mem_cons_of_mem _ hu)
  have hpU := List.perm_cons_erase huF
  exact ⟨hne,component_cycle u _ (balanced_perm hpU hb) (noCross_perm hpU hc) hne⟩

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarNormal.Proof
