module
public import LogicLineages.OrdinalComparison.Definitions
public import Mathlib.Data.Nat.Pairing

@[expose] public section

/-! Explicit faithful-code candidate for raw hereditary ordinal notation.
Zero has code zero; a monomial node uses successor of nested natural pairing,
with its positive coefficient stored minus one. Every natural code decodes to
a raw tree, because both recursive child codes are strictly smaller.
This defines neither a code for the normal subtype nor any effectiveness
certificate for comparison, norm, arithmetic, finite balls or collapse.
-/

namespace LogicLineages.OrdinalComparison

def rawNoteEncode : ONote → Nat
  | .zero => 0
  | .oadd e c t => Nat.pair (rawNoteEncode e) (Nat.pair ((c : Nat) - 1) (rawNoteEncode t)) + 1

def rawNoteDecode : Nat → ONote
  | 0 => .zero
  | n + 1 => .oadd (rawNoteDecode n.unpair.1)
      ⟨n.unpair.2.unpair.1 + 1, Nat.succ_pos _⟩ (rawNoteDecode n.unpair.2.unpair.2)
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_of_le (Nat.unpair_left_le n)
  · exact Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le n))

end LogicLineages.OrdinalComparison
