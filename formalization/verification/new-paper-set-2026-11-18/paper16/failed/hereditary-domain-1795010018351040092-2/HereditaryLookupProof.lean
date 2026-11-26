import LogicLineages.PersistentMarking.HereditaryDomainTargets
import LogicLineages.PersistentMarking.FiniteEqualityProof
import LogicLineages.PersistentMarking.FiniteVectorProof
namespace LogicLineages.PersistentMarking.HereditaryLookupProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode

theorem kindExact (a b : Kind) : kindEq a b = true ↔ a=b := by
  cases a <;> cases b <;> simp [kindEq,FiniteEqualityProof.expr,and_assoc]

theorem keyExact (a b : Key) : keyEq a b = true ↔ a=b := by
  cases a; cases b
  simp [keyEq,kindExact,Key.mk.injEq]

theorem indexSound (codes : List Code) (v : Code) (i : Nat) (h : indexOf codes v = some i) :
    codes[i]? = some v := by
  induction codes generalizing i with
  | nil => cases h
  | cons c cs ih =>
    by_cases he : c=v
    · subst c
      simp only [indexOf,decide_true,if_true,Option.some.injEq] at h
      subst i; rfl
    · simp only [indexOf,decide_eq_false_iff_not.mpr he,if_false] at h
      cases hh : indexOf cs v with
      | none => simp [hh] at h
      | some j =>
        simp only [hh,Option.map_some,Option.some.injEq] at h
        subst i
        exact ih j hh

theorem indexAt (codes : List Code) (v : Code) (i : Nat)
    (hd : codes.Pairwise (· ≠ ·)) (hi : codes[i]? = some v) :
    indexOf codes v = some i := by
  induction codes generalizing i with
  | nil => cases i <;> cases hi
  | cons c cs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hi
      subst v
      simp [indexOf]
    | succ i =>
      have hn : c ≠ v := (List.pairwise_cons.mp hd).1 v (List.mem_of_getElem? hi)
      have hr := ih i (List.pairwise_cons.mp hd).2 hi
      simp [indexOf,hn,hr]

theorem indexExists (codes : List Code) (v : Code) : v ∈ codes → ∃ i, indexOf codes v = some i := by
  induction codes with
  | nil => intro h; cases h
  | cons c cs ih =>
    intro h
    by_cases he : c=v
    · subst c; exact ⟨0,by simp [indexOf]⟩
    · have hv : v ∈ cs := (List.mem_cons.mp h).elim (fun h => False.elim (he h.symm)) id
      obtain ⟨i,hi⟩ := ih hv
      exact ⟨i+1,by simp [indexOf,he,hi]⟩

theorem lookupAt (schema : List (Key × Nat)) (code : Code) (i : Nat) (key : Key) (bound value : Nat)
    (hs : (schema.map Prod.fst).Pairwise (· ≠ ·))
    (hk : schema[i]? = some (key,bound)) (hv : code[i]? = some value) :
    lookup schema code key = some value := by
  induction schema generalizing code i with
  | nil => cases i <;> cases hk
  | cons kb ks ih =>
    cases code with
    | nil => cases i <;> cases hv
    | cons v vs =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at hk hv
        cases hk; cases hv
        simp [lookup,(keyExact key key).mpr rfl]
      | succ i =>
        have hn : kb.1 ≠ key := (List.pairwise_cons.mp hs).1 key
          (List.mem_map.mpr ⟨(key,bound),List.mem_of_getElem? hk,rfl⟩)
        have he : keyEq kb.1 key = false := Bool.eq_false_iff.mpr (fun h => hn ((keyExact _ _).mp h))
        simp only [lookup,he,Bool.false_eq_true,if_false]
        exact ih vs i (List.pairwise_cons.mp hs).2 hk hv

theorem lookupBound (schema : List (Key × Nat)) (code : Code) (key : Key) (value : Nat)
    (hf : Fits (schema.map Prod.snd) code) (h : lookup schema code key = some value) :
    ∃ bound, (key,bound) ∈ schema ∧ value<bound := by
  induction schema generalizing code with
  | nil => cases h
  | cons kb ks ih =>
    cases code with
    | nil => cases hf
    | cons v vs =>
      by_cases he : keyEq kb.1 key = true
      · have hk := (keyExact _ _).mp he
        simp only [lookup,he,if_true,Option.some.injEq] at h
        cases h
        exact ⟨kb.2,List.mem_cons.mpr (Or.inl (by cases kb; simp_all)),hf.1⟩
      · simp only [lookup,if_neg he] at h
        obtain ⟨bound,hb,hv⟩ := ih vs hf.2 h
        exact ⟨bound,List.mem_cons_of_mem _ hb,hv⟩
end LogicLineages.PersistentMarking.HereditaryLookupProof
