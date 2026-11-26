module
public import LogicLineages.PermittedControl.OriginalPrintedTerminalBitClausesTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedTerminalBitClauses
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)

private theorem vectorMember (n : Nat) (bits : List Bool) : bits ∈ vectors n ↔ bits.length = n := by
  induction n generalizing bits with
  | zero => cases bits <;> simp [vectors]
  | succ n ih =>
    cases bits with
    | nil => simp [vectors]
    | cons b bs => cases b <;> simp [vectors,ih]

theorem exactAcceptedVectors : ExactAcceptedVectors := by
  intro p positive n bits
  simp only [accepted,List.mem_filter,decide_eq_true_eq,vectorMember]

theorem exactBitTape : ExactBitTape := by
  intro f ρ rows
  induction rows with
  | nil =>
    intro bits size
    cases bits with
    | nil =>
      exact ⟨fun _ => ⟨[],True.intro,rfl⟩,fun _ p used => False.elim (List.not_mem_nil used)⟩
    | cons b bs => cases size
  | cons r rs ih =>
    intro bits size
    cases bits with
    | nil => cases size
    | cons b bs =>
      have len : bs.length = rs.length := Nat.succ.inj size
      constructor
      · intro all
        obtain ⟨admitted,v,value,sign⟩ := all (r,b) List.mem_cons_self
        obtain ⟨snap,h,vals⟩ := (ih bs len).mp
          (fun row used => all row (List.mem_cons_of_mem _ used))
        exact ⟨(v,b)::snap,⟨admitted,value,sign,h⟩,congrArg (List.cons b) vals⟩
      · rintro ⟨snap,h,vals⟩
        cases snap with
        | nil => exact False.elim h
        | cons first tail =>
          have bitsEq : first.2 :: tail.map Prod.snd = b :: bs := vals
          have head : first.2 = b := (List.cons.inj bitsEq).1
          have other := (ih bs len).mpr ⟨tail,h.2.2.2,(List.cons.inj bitsEq).2⟩
          intro row used
          rcases List.mem_cons.mp used with eq | rest
          · subst row
            exact ⟨h.1,first.1,h.2.1,head ▸ h.2.2.1⟩
          · exact other row rest

end LogicLineages.PermittedControl.OriginalPrintedTerminalBitClauses
