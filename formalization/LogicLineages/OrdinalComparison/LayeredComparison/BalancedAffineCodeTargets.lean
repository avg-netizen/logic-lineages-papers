module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineCodeDefinitions
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineCode.Targets
open BalancedSyntax BalancedEvaluation

/-- Exact code equality with the existing literal source operations, at every
shape including BASE. This is stronger than an equality of evaluated values. -/
def ExactLiteralOperations : Prop := ∀ Γ : List Nat,
  (∀ n, numeral Γ n=encodeSyntax Γ (Affine.numeral Γ n)) ∧
  (∀ E F : Syntax Γ,
    add Γ (encodeSyntax Γ E) (encodeSyntax Γ F)=encodeSyntax Γ (Affine.add Γ E F)) ∧
  (∀ (n : Nat) (E : Syntax Γ),
    scale Γ n (encodeSyntax Γ E)=encodeSyntax Γ (Affine.scale Γ n E))

/-- The full ordered list of the actual finite basis is used. Repeated or
dependent basis entries and zero outside coefficients are unrestricted. -/
def ExactFiniteCombination : Prop := ∀ (Γ : List Nat) (k c : Nat)
  (coefficients : Fin k → Nat) (basis : Fin k → Syntax Γ),
  combination Γ k c (List.ofFn coefficients) (List.ofFn (fun j => encodeSyntax Γ (basis j)))=
    encodeSyntax Γ (Affine.combination Γ k c coefficients basis)

/-- Both outputs are the actual preceding-level source syntax under C.1.
The existing encodeAtom payload is used unchanged; every outer coefficient q
gives the same complete input. No genuine-head hypothesis is needed for these
syntactic equalities, and no malformed raw code is claimed source-valid. -/
def ExactActualLowerAndInputs : Prop := ∀ (k : Nat) (Γ : List Nat)
  (C : Certificate (k::Γ)) (E : Upper k) (a : Atom k) (q : Nat),
  lowerPart k Γ (encodeCertificate (k::Γ) C) (encodeSyntax (k::Γ) E)=
    encodeSyntax Γ (Affine.lowerPart k Γ C E) ∧
  completeInput k Γ (encodeCertificate (k::Γ) C) (Encodable.encode (encodeAtom (q,a)))=
    encodeSyntax Γ (Affine.completeInput k Γ C a)

/-- Uniform primitive recursion on ALL finite numeric inputs and shapes, not
only on fixed certificates or valid source encodings. The complete-input
constructor requires only the already established primitive recursive norm. -/
def UniformPrimitiveRecursive : Prop :=
  Primrec (fun p : List Nat × Nat => numeral p.1 p.2) ∧
  Primrec (fun p : List Nat × Nat × Nat => add p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : List Nat × Nat × Nat => scale p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : List Nat × Nat × Nat × List Nat × List Nat =>
    combination p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∧
  Primrec (fun p : Nat × List Nat × Nat × Nat => lowerPart p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Nat × List Nat × Nat × Nat => completeInput p.1 p.2.1 p.2.2.1 p.2.2.2)

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineCode.Targets
