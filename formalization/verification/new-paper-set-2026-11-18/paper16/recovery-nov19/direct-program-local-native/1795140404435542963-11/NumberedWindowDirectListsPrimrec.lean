module

public import LogicLineages.PersistentMarking.NumberedWindowDirectProgramTargets

public section
namespace LogicLineages.PersistentMarking.NumberedWindowDirectListsPrimrec
open NumberedWindowDirectAlgorithm

private theorem permutation : Primrec₂ (fun (xs ys : List Nat) => decide (xs.Perm ys)) := by
  have count : Primrec₂ (fun (xs : List Nat) (a : Nat) => xs.count a) := by
    have h := Primrec.list_length.comp (PrimrecRel.listFilter (Primrec.eq : PrimrecRel (Eq : Nat → Nat → Prop)))
    apply h.to₂.of_eq
    intro xs a
    simp [List.count_eq_length_filter]
  have same : PrimrecRel (fun (a : Nat) (p : List Nat × List Nat) => p.1.count a = p.2.count a) :=
    Primrec.eq.comp (count.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (count.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
  have bounded := same.forall_mem_list.comp (Primrec.list_append.comp Primrec.fst Primrec.snd) Primrec.id
  apply (bounded.of_eq ?_).decide
  intro p
  rw [List.perm_iff_count]
  constructor
  · intro h a
    by_cases ha : a ∈ p.1 ++ p.2
    · exact h a ha
    · have h₁ : a ∉ p.1 := fun h => ha (List.mem_append_left _ h)
      have h₂ : a ∉ p.2 := fun h => ha (List.mem_append_right _ h)
      simp [List.count_eq_zero_of_not_mem h₁, List.count_eq_zero_of_not_mem h₂]
  · exact fun h a _ => h a

theorem allWith {α γ} [Primcodable α] [Primcodable γ] {f : α → γ → Bool} (h : Primrec₂ f) :
    Primrec₂ (fun (xs : List α) (c : γ) => xs.all (fun a => f a c)) := by
  have yes : PrimrecRel (fun a c => f a c = true) := Primrec.eq.comp h (Primrec.const true)
  apply yes.forall_mem_list.decide.to₂.of_eq
  intro xs c
  apply Bool.eq_iff_iff.mpr
  simp

theorem allScalar {scalar : Nat → Bool} (hs : Primrec scalar) : Primrec (fun xs : List Nat => xs.all scalar) := by
  have single : Primrec₂ (fun (a : Nat) (_ : Unit) => scalar a) := hs.comp Primrec.fst
  exact (allWith single).comp Primrec.id (Primrec.const ())

abbrev Inputs := List Nat × List Nat × Witness

theorem directListsPrimitive (scalar : Nat → Bool) (positive : Nat → Nat → Nat → Bool)
    (hs : Primrec scalar) (hp : Primrec (fun p : Entry => positive p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Inputs => directLists scalar positive p.1 p.2.1 p.2.2) := by
  have src : Primrec (fun p : Inputs => p.1) := Primrec.fst
  have dst : Primrec (fun p : Inputs => p.2.1) := Primrec.fst.comp Primrec.snd
  have wit : Primrec (fun p : Inputs => p.2.2) := Primrec.snd.comp Primrec.snd
  have kept : Primrec (fun p : Inputs => p.2.2.1) := Primrec.fst.comp wit
  have removed : Primrec (fun p : Inputs => p.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp wit)
  have inserted : Primrec (fun p : Inputs => p.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp wit)
  have targets : Primrec (fun p : Inputs => p.2.2.2.2.map Prod.fst) :=
    Primrec.list_map inserted (Primrec.fst.comp Primrec.snd).to₂
  have has : PrimrecRel (fun (xs : List Nat) (a : Nat) => a ∈ xs) :=
    (Primrec.eq : PrimrecRel (Eq : Nat → Nat → Prop)).exists_mem_list.of_eq (by simp)
  have dom : Primrec (fun p : Entry × List Nat => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have cert : Primrec (fun p : Entry × List Nat => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have target : Primrec (fun p : Entry × List Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have witnesses := allWith (Primrec.and.comp ((has.comp Primrec.snd dom).decide)
    (hp.comp (dom.pair (cert.pair target)))).to₂
  have alive : Primrec (fun p : Inputs => !p.2.2.2.1.isEmpty) :=
    ((Primrec.eq.comp removed (Primrec.const [])).not.decide).of_eq (fun p => by
      cases p.2.2.2.1 <;> simp)
  exact Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp
    (Primrec.and.comp ((allScalar hs).comp src) ((allScalar hs).comp dst))
    (permutation.comp src (Primrec.list_append.comp kept removed)))
    (permutation.comp dst (Primrec.list_append.comp kept targets))) alive)
    (witnesses.comp inserted removed)

end LogicLineages.PersistentMarking.NumberedWindowDirectListsPrimrec
