module
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeDefinitions
public import LogicLineages.OrdinalComparison.WWDefaultPolicyDefinitions
public import LogicLineages.OrdinalComparison.WWSourceComparisonDefinitions
public import Mathlib.Computability.RE
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalInput
open ForwardTranslation OrdinalSyntax

/-- Common ground-context arity, strictness flag, and two literal original-T
codes. Output and internal types are not restricted. -/
abbrev Query := Nat × Bool × Nat × Nat

def context (q : Query) : List Ty := List.replicate q.1 Ty.ground

/-- Invalid product encodings default to two malformed tag-7 T codes.
Universal source predicates below are vacuously true on unrepresentable
queries; this is a total numerical extension, not a premise on source terms. -/
def decode (n : Nat) : Query := (Encodable.decode n).getD (0, false, 7, 7)

noncomputable def Point (q : Query) (xs : List Nat) : Prop :=
  ∀ (τ υ : Ty) (a : OriginalTerm (context q) τ) (b : OriginalTerm (context q) υ)
    (av : OrdinalVector (context q) τ.level) (bv : OrdinalVector (context q) υ.level),
    SyntaxCode.encodeTerm a = q.2.2.1 → SyntaxCode.encodeTerm b = q.2.2.2 →
    AdmissibleAssignment.assignment defaultPolicy a = some av →
    AdmissibleAssignment.assignment defaultPolicy b = some bv →
    SourceComparisonAt q.2.1 av bv (fun c => xs.getD (SourceTypedPorts.variableIndex c.2.1) 0 + 1)

noncomputable def Good (q : Query) : Prop :=
  ∀ (τ υ : Ty) (a : OriginalTerm (context q) τ) (b : OriginalTerm (context q) υ)
    (av : OrdinalVector (context q) τ.level) (bv : OrdinalVector (context q) υ.level),
    SyntaxCode.encodeTerm a = q.2.2.1 → SyntaxCode.encodeTerm b = q.2.2.2 →
    AdmissibleAssignment.assignment defaultPolicy a = some av →
    AdmissibleAssignment.assignment defaultPolicy b = some bv →
    ∀ ρ : OrdinalComponent (context q) → Nat, (∀ c, 0 < ρ c) → SourceComparisonAt q.2.1 av bv ρ

noncomputable def CodedGood (n : Nat) : Prop := Good (decode n)

noncomputable def CoordinateBound : Prop :=
  ∃ b : Nat → Nat, Computable b ∧ ∀ n, ¬ CodedGood n →
    ∃ xs : List Nat, xs.length = (decode n).1 ∧
      (∀ x ∈ xs, x+1 ≤ b n) ∧ ¬ Point (decode n) xs
end LogicLineages.OrdinalComparison.Source.OriginalInput
