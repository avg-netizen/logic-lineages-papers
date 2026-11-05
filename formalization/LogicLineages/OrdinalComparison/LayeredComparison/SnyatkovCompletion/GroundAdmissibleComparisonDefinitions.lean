module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.RecursorFreeVectorDefinitions
public import LogicLineages.OrdinalComparison.WWOriginalDomainDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.GroundAdmissibleComparison
open Source Source.OriginalDomain

/-- The original ordinal interpretation under a genuine closed, graded,
bounded WW substitution. Coordinates outside the actual vector are the
original literal Zero padding, rather than an independently chosen value. -/
noncomputable def vectorAtValue {Γ : List Ty} {n : Nat}
    (v : OrdinalVector Γ n) (ρ : AdmissibleSubstitution Γ) (j : Nat) : Ordinal :=
  expressionValue ρ (ordinalVectorAt v j)

/-- Original universal-comparison modes at one admissible substitution.
Weak comparison is weak at every coordinate; WW-strict comparison is strict
only at coordinate zero and weak above it. Equality compares all coordinates.
Modes 0, 1, and every other natural code agree with the existing source API. -/
noncomputable def relation {Γ : List Ty} {n m : Nat} (mode : Nat)
    (a : OrdinalVector Γ n) (b : OrdinalVector Γ m)
    (ρ : AdmissibleSubstitution Γ) : Prop :=
  if mode = 0 then
    (∀ j : Nat, vectorAtValue a ρ (j + 1) ≤ vectorAtValue b ρ (j + 1)) ∧
      vectorAtValue a ρ 0 ≤ vectorAtValue b ρ 0
  else if mode = 1 then
    (∀ j : Nat, vectorAtValue a ρ (j + 1) ≤ vectorAtValue b ρ (j + 1)) ∧
      vectorAtValue a ρ 0 < vectorAtValue b ρ 0
  else ∀ j : Nat, vectorAtValue a ρ j = vectorAtValue b ρ j

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.GroundAdmissibleComparison
