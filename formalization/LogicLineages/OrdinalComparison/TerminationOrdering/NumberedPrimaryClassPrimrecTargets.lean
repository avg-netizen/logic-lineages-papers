module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryClassPrimrecDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedCodecPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryClassPrimrecTargets
open Source NumberedRewriteReduction NumberedPrimaryClassPrimrec

local instance {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    {Gamma : List Ty} : DecidableEq (Packed Symbol arity Gamma) :=
  NumberedAuxiliaryCodingProof.packedDecidableEq

/-- Every list iterate represents the exact original finite-set iterate. -/
def ActualReachableListCalibration : Prop :=
  ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (symbols : List Symbol) (S Gamma : List Ty) (q : Packed Symbol arity Gamma)
    (fuel : Nat),
    (reachableList symbols S q fuel).toFinset =
      NumberedFinitePrimaryClass.reachable symbols S q fuel

/-- The list-length cutoff represents the exact original primary class. -/
def ActualPrimaryListCalibration : Prop :=
  ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (symbols : List Symbol) (S Gamma : List Ty) (q : Packed Symbol arity Gamma),
    (primaryList symbols S q).toFinset =
      NumberedFinitePrimaryClass.primaryClass symbols S q

/-- Joint effectivity in both actual window lists and the genuinely presented seed. -/
def ActualPrimaryListPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : (List (Fin n) × List Ty) × Packed (Fin n) arity Gamma =>
      primaryList p.1.1 p.1.2 p.2)

/-- Primitive recursion of the original primary-class membership test itself. -/
def ActualPrimaryTestPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : (List (Fin n) × List Ty) ×
        Packed (Fin n) arity Gamma × Packed (Fin n) arity Gamma =>
      NumberedFinitePrimaryClass.primaryTest p.1.1 p.1.2 p.2.1 p.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryClassPrimrecTargets
