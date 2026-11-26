module
public import LogicLineages.PermittedControl.ClosedOrdinaryFieldTargets
import LogicLineages.PermittedControl.ClosedOrdinaryFieldResultProof

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

private theorem mapped_none {α β : Type*} (r : Option (Option α)) (g : α → β) :
    r.map (fun s => s.map g) = none ↔ r = none := by
  cases r <;> simp

private theorem mapped_miss {α β : Type*} (r : Option (Option α)) (g : α → β) :
    r.map (fun s => s.map g) = some none ↔ r = some none := by
  cases r with
  | none => simp
  | some s => cases s <;> simp

private theorem mapped_hit {α β : Type*} (r : Option (Option α)) (g : α → β) (v : β) :
    r.map (fun s => s.map g) = some (some v) ↔
      ∃ e : α, r = some (some e) ∧ g e = v := by
  cases r with
  | none => simp
  | some s =>
    cases s with
    | none => simp
    | some e =>
      constructor
      · intro h
        exact ⟨e,rfl,Option.some.inj (Option.some.inj h)⟩
      · rintro ⟨e',he,hv⟩
        have he' : e = e' := Option.some.inj (Option.some.inj he)
        subst e'
        exact congrArg (fun x => some (some x)) hv

theorem closedOrdinaryValueActual : ClosedOrdinaryValueActual := by
  intro f F x
  cases F with
  | iterate a =>
    simp only [closedOrdinaryValueField,longFieldCode,ite_true,ClosedOrdinaryValueDomain,FieldValue]
    refine ⟨by simp,fun _ => ⟨fun v => by simp [eq_comm],?_⟩⟩
    constructor
    · intro h
      cases Option.some.inj h
    · intro h
      exact (h (f^[a] x) rfl).elim
  | entry a lam mu =>
    simp only [closedOrdinaryValueField,longFieldCode,one_ne_zero,ite_false]
    rw [mapped_none]
    refine ⟨proper_entry_none_iff f lam mu x,?_⟩
    intro hd
    have hs := closedProperEntryResultExact.2 f lam mu x hd
    refine ⟨?_,?_⟩
    · intro v
      rw [mapped_hit]
      constructor
      · rintro ⟨⟨E,i⟩,hr,hv⟩
        obtain ⟨hi,hE⟩ := (hs.1 E i).mp hr
        exact ⟨i,hi,by simpa only [hE] using hv.symm⟩
      · rintro ⟨i,hi,hv⟩
        exact ⟨(entryNormAt f (countInitial lam.1.repr x) i,i),
          (hs.1 _ i).mpr ⟨hi,rfl⟩,hv.symm⟩
    · rw [mapped_miss,hs.2]
      constructor
      · intro hnone v hv
        obtain ⟨i,hi,_⟩ := hv
        exact hnone i hi
      · intro hnone i hi
        exact hnone (f^[a] (entryNormAt f (countInitial lam.1.repr x) i)) ⟨i,hi,rfl⟩

theorem closedOrdinaryCountActual : ClosedOrdinaryCountActual := by
  intro f lam mu x
  simp only [closedOrdinaryCountField]
  rw [mapped_none]
  refine ⟨proper_entry_none_iff f lam mu x,?_⟩
  intro hd
  have hs := closedProperEntryResultExact.2 f lam mu x hd
  refine ⟨?_,?_⟩
  · intro i
    rw [mapped_hit]
    constructor
    · rintro ⟨⟨E,j⟩,hr,hj⟩
      change j = i at hj
      subst j
      exact ((hs.1 E i).mp hr).1
    · intro hi
      exact ⟨(entryNormAt f (countInitial lam.1.repr x) i,i),
        (hs.1 _ i).mpr ⟨hi,rfl⟩,rfl⟩
  · rw [mapped_miss,hs.2]

end LogicLineages.PermittedControl.FieldComparison
