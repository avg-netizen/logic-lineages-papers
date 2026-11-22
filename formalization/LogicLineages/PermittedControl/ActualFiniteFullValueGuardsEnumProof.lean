module
public import LogicLineages.PermittedControl.ActualFiniteFullValueGuardsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFiniteFullValueGuards
open ActualFullLabelPairGuards (Answer choices)

private theorem allChoices (a : Answer) : a ∈ choices := by
  cases a <;> simp [choices]

theorem exactFinitePatternEnumeration : ExactFinitePatternEnumeration := by
  intro n
  induction n with
  | zero =>
      intro as
      cases as <;> simp [patterns]
  | succ n ih =>
      intro as
      cases as with
      | nil =>
          constructor
          · intro member
            obtain ⟨a,_,inside⟩ := List.mem_flatMap.mp member
            obtain ⟨xs,_,eq⟩ := List.mem_map.mp inside
            cases eq
          · intro empty
            exact False.elim ((Nat.succ_ne_zero n) empty.symm)
      | cons a as =>
          constructor
          · intro member
            obtain ⟨b,_,inside⟩ := List.mem_flatMap.mp member
            obtain ⟨bs,other,h⟩ := List.mem_map.mp inside
            have same := (List.cons.inj h).2
            subst bs
            have arity := (ih as).mp other
            simp only [List.length_cons,arity]
          · intro arity
            have len : as.length = n := Nat.succ.inj arity
            exact List.mem_flatMap.mpr ⟨a,allChoices a,List.mem_map.mpr ⟨as,(ih as).mpr len,rfl⟩⟩

end LogicLineages.PermittedControl.ActualFiniteFullValueGuards
