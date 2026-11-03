module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineSyntaxDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntax.Affine.Targets

def LiteralAffineClosure : Prop := ∀ (Γ : List Nat) (C : Certificate Γ) (ν : Nat → Nat),
  (∀ n, value Γ C (numeral Γ n) ν=n ∧ genuineExpression Γ (numeral Γ n)) ∧
  (∀ E F, value Γ C (add Γ E F) ν=value Γ C E ν+value Γ C F ν ∧
    (genuineExpression Γ E → genuineExpression Γ F → genuineExpression Γ (add Γ E F))) ∧
  (∀ n E, value Γ C (scale Γ n E) ν=n*value Γ C E ν ∧
    (genuineExpression Γ E → genuineExpression Γ (scale Γ n E)))

def ExactAffineSupport : Prop := ∀ (Γ : List Nat) (C : Certificate Γ),
  (∀ n, rawVariables Γ C (numeral Γ n)=[]) ∧
  (∀ E F i, i∈rawVariables Γ C (add Γ E F) ↔
    i∈rawVariables Γ C E ∨ i∈rawVariables Γ C F) ∧
  (∀ n E i, i∈rawVariables Γ C (scale Γ n E) ↔ n≠0 ∧ i∈rawVariables Γ C E)

/-- One shared lower certificate and basis throughout; repeated/dependent basis
entries are allowed. Exact supports discard zero outside coefficients only. -/
def ActualLowerAndInputs : Prop := ∀ (k : Nat) (Γ : List Nat) (C : Certificate (k::Γ))
  (E : Upper k) (a : Atom k) (ν : Nat → Nat),
  value Γ C.1 (lowerPart k Γ C E) ν =
    E.constant+((List.ofFn E.outside).zipWith (·*·) (basisValues k Γ C ν)).sum ∧
  value Γ C.1 (completeInput k Γ C a) ν =
    BalancedRow.input (basisValues k Γ C ν) (asAtom a) ∧
  (∀ i, i∈rawVariables Γ C.1 (lowerPart k Γ C E) ↔
    ∃ j : Fin k, E.outside j≠0 ∧ i∈rawVariables Γ C.1 (C.2 j)) ∧
  (∀ i, i∈rawVariables Γ C.1 (completeInput k Γ C a) ↔
    ∃ j : Fin k, i∈rawVariables Γ C.1 (C.2 j)) ∧
  (genuineCertificate (k::Γ) C →
    genuineExpression Γ (lowerPart k Γ C E) ∧ genuineExpression Γ (completeInput k Γ C a))

/-- All cancellation descends to two LITERAL preceding-level source terms,
not a new integer-valued oracle or independent basis assignment. -/
def ActualCanceledDescent : Prop := ∀ (k : Nat) (Γ : List Nat) (C : Certificate (k::Γ))
  (E F : Upper k) (ν : Nat → Nat),
  (BalancedRow.Collection.collect (basisValues k Γ C ν) (comparisonRow E F)).atoms=[] →
  (value (k::Γ) C E ν : Int)-(value (k::Γ) C F ν : Int)=
    (value Γ C.1 (lowerPart k Γ C E) ν : Int)-(value Γ C.1 (lowerPart k Γ C F) ν : Int)
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntax.Affine.Targets
