module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeCodecPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadCodecPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeView
open Source NumberedAuxiliaryCoding

/-- One constructor layer, preserving every original field and recursive child. -/
abbrev CodeView (n : Nat) :=
  Nat ⊕ ((Ty × Code (Fin n)) ⊕ ((Ty × Code (Fin n) × Code (Fin n)) ⊕
    (Ty ⊕ ((HeadCode (Fin n) × Code (Fin n)) ⊕
      ((Nat × HeadCode (Fin n) × Ty × Code (Fin n) × List Ty × Code (Fin n)) ⊕
        (Unit ⊕ (Ty × Code (Fin n) × Code (Fin n))))))))

def view {n : Nat} : Code (Fin n) → CodeView n
  | .var index => .inl index
  | .lam sigma body => .inr (.inl (sigma, body))
  | .app sigma q a => .inr (.inr (.inl (sigma, q, a)))
  | .bottom tau => .inr (.inr (.inr (.inl tau)))
  | .ordinary head base => .inr (.inr (.inr (.inr (.inl (head, base)))))
  | .numbered k head tau base types extras =>
    .inr (.inr (.inr (.inr (.inr (.inl (k, head, tau, base, types, extras))))))
  | .argumentsNil => .inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))
  | .argumentsCons tau q rest =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (tau, q, rest)))))))

def unview {n : Nat} : CodeView n → Code (Fin n)
  | .inl index => .var index
  | .inr (.inl (sigma, body)) => .lam sigma body
  | .inr (.inr (.inl (sigma, q, a))) => .app sigma q a
  | .inr (.inr (.inr (.inl tau))) => .bottom tau
  | .inr (.inr (.inr (.inr (.inl (head, base))))) => .ordinary head base
  | .inr (.inr (.inr (.inr (.inr (.inl (k, head, tau, base, types, extras)))))) =>
    .numbered k head tau base types extras
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))) => .argumentsNil
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (tau, q, rest))))))) =>
    .argumentsCons tau q rest

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeView
