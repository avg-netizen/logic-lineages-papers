module
public import LogicLineages.PermittedControl.SelectedGeneratedSourceTargets
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.PermittedControl.GroundComparison
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.ForwardTranslation
open SelectedSourceDomain

/-- The three comparisons of `paper.tex` l.76–80. -/
inductive Relation where
  | weak
  | strict
  | equal

/-- Coordinate `j` of an assigned vector under an admissible substitution,
with zero padding beyond the vector's level. -/
noncomputable def vectorAt (ctrl : Nat → Nat) {Γ : List Ty} {n : Nat} (v : OrdinalVector Γ n)
    (s : AdmissibleSubstitution ctrl Γ) (j : Nat) : Ordinal.{0} :=
  if h : j < n+1 then expressionValue ctrl s (v ⟨j,h⟩) else 0

/-- Weak comparison: universal coordinatewise inequality under all
admissible valuations. Wilken–Weiermann strict comparison: universal strict
inequality in coordinate zero and universal weak inequality in every
positive coordinate. Equality: universal coordinatewise equality. -/
def Holds (ctrl : Nat → Nat) {Γ : List Ty} {n m : Nat} :
    Relation → OrdinalVector Γ n → OrdinalVector Γ m → Prop
  | .weak, a, b => ∀ (s : AdmissibleSubstitution ctrl Γ) (j : Nat), vectorAt ctrl a s j ≤ vectorAt ctrl b s j
  | .strict, a, b =>
      (∀ s : AdmissibleSubstitution ctrl Γ, vectorAt ctrl a s 0 < vectorAt ctrl b s 0) ∧
      ∀ (s : AdmissibleSubstitution ctrl Γ) (j : Nat), 0 < j → vectorAt ctrl a s j ≤ vectorAt ctrl b s j
  | .equal, a, b => ∀ (s : AdmissibleSubstitution ctrl Γ) (j : Nat), vectorAt ctrl a s j = vectorAt ctrl b s j

/-- The comparison of the canonical assignments of the two literal terms
under the supplied policy. -/
def Canonical (ctrl : Nat → Nat) (p : Policy) (rel : Relation) {Γ : List Ty} {τ υ : Ty}
    (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ) : Prop :=
  ∃ (av : OrdinalVector Γ τ.level) (bv : OrdinalVector Γ υ.level),
    AdmissibleAssignment.assignment p a = some av ∧ AdmissibleAssignment.assignment p b = some bv ∧
    Holds ctrl rel av bv

/-- For one control: for every computable admissible policy and each of the
three relations, one computable procedure decides the relation on all pairs
of original terms whose free variables all have ground type, of arbitrary
result, internal and bound-variable types. The input is the context length
and the two literal term codes. -/
def GroundDecidable (ctrl : Nat → Nat) : Prop :=
  ∀ p : Policy, StandardControlCurrent.PolicyShape.Effective p → ∀ rel : Relation,
    ∃ decide : Nat × Nat × Nat → Bool, Computable decide ∧
      ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) → ∀ (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ),
        (decide (Γ.length,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b) = true ↔
          Canonical ctrl p rel a b)

/-- Comparator for Paper 17 `thm:ground`: both controls. -/
def GroundComparison : Prop :=
  GroundDecidable factorialControl ∧ ∀ b : Nat, GroundDecidable (nearControl b)

end LogicLineages.PermittedControl.GroundComparison
