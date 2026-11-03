module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadCodecPrimrec
open Source NumberedAuxiliaryCoding NumberedTypeCodecPrimrec

abbrev HeadData (n : Nat) := Bool ⊕ (Ty ⊕ (Ty ⊕ ((Ty × Ty) ⊕ Fin n)))

def headEquiv (n : Nat) : HeadCode (Fin n) ≃ HeadData n where
  toFun
    | .zero => .inl false
    | .succ => .inl true
    | .cases tau => .inr (.inl tau)
    | .recursor tau => .inr (.inr (.inl tau))
    | .application sigma tau => .inr (.inr (.inr (.inl (sigma,tau))))
    | .ranked s => .inr (.inr (.inr (.inr s)))
  invFun
    | .inl false => .zero
    | .inl true => .succ
    | .inr (.inl tau) => .cases tau
    | .inr (.inr (.inl tau)) => .recursor tau
    | .inr (.inr (.inr (.inl (sigma,tau)))) => .application sigma tau
    | .inr (.inr (.inr (.inr s))) => .ranked s
  left_inv q := by cases q <;> rfl
  right_inv q := by
    rcases q with b | tau | tau | ⟨sigma,tau⟩ | s
    · cases b <;> rfl
    all_goals rfl

instance headPrimcodable (n : Nat) : Primcodable (HeadCode (Fin n)) := Primcodable.ofEquiv _ (headEquiv n)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadCodecPrimrec
