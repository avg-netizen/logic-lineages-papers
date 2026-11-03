module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeCodecPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedRequestsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestPresentation
open Source NumberedAuxiliaryCoding NumberedTypedRequests

/-- The two request constructors with every source field preserved literally. -/
abbrev RequestData (n : Nat) :=
  (List Ty × Ty × Code (Fin n)) ⊕ (List Ty × List Ty × Code (Fin n))

def requestEquiv (n : Nat) : Request n ≃ RequestData n where
  toFun
    | .term Gamma tau code => .inl (Gamma, tau, code)
    | .arguments Gamma types code => .inr (Gamma, types, code)
  invFun
    | .inl (Gamma, tau, code) => .term Gamma tau code
    | .inr (Gamma, types, code) => .arguments Gamma types code
  left_inv request := by cases request <;> rfl
  right_inv data := by
    rcases data with ⟨Gamma, tau, code⟩ | ⟨Gamma, types, code⟩ <;> rfl

instance requestPrimcodable (n : Nat) : Primcodable (Request n) :=
  Primcodable.ofEquiv (RequestData n) (requestEquiv n)

theorem requestToPrimitive (n : Nat) : Primrec (requestEquiv n) :=
  Primrec.of_equiv

theorem requestFromPrimitive (n : Nat) : Primrec (requestEquiv n).symm :=
  Primrec.of_equiv_symm

theorem termRequestPrimitive (n : Nat) :
    Primrec (fun p : List Ty × Ty × Code (Fin n) => Request.term p.1 p.2.1 p.2.2) :=
  (requestFromPrimitive n).comp Primrec.sumInl

theorem argumentsRequestPrimitive (n : Nat) :
    Primrec (fun p : List Ty × List Ty × Code (Fin n) => Request.arguments p.1 p.2.1 p.2.2) :=
  (requestFromPrimitive n).comp Primrec.sumInr

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestPresentation
