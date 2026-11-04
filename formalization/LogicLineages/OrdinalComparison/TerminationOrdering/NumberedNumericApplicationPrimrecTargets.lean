module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationPrimrecDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationPrimrecTargets
open Source NumberedNumericApplication NumberedNumericApplicationPrimrec

def ActualApplicationProgramCalibration : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (sigma tau : Ty) (x y : Nat),
    applicationProgram n arity symbols S Gamma sigma tau x y = canonicalApplication n arity symbols S Gamma sigma tau x y

def ActualCanonicalApplicationPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : (List (Fin n) × List Ty) × Ty × Ty × Nat × Nat =>
      canonicalApplication n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationPrimrecTargets
