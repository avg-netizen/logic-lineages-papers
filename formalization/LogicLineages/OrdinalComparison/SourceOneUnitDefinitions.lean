module
public import LogicLineages.OrdinalComparison.WWSelectedBinderDefinitions
public import LogicLineages.OrdinalComparison.WWDefaultPolicyDefinitions
public import LogicLineages.OrdinalComparison.WWOriginalDomainDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OneUnit
open AdmissibleAssignment OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def unused {Γ τ} (a : OriginalTerm Γ τ) : OriginalTerm Γ (.arrow .ground τ) :=
  .lam (a.rename (Renaming.weaken Γ .ground))

def first {Γ σ τ} (a : OriginalTerm (σ :: Γ) τ) : OriginalTerm Γ (.arrow σ τ) := .lam a

def second {Γ σ τ} (a : OriginalTerm (σ :: Γ) τ) : OriginalTerm Γ (.arrow σ (.arrow .ground τ)) :=
  .lam (unused a)

def multiplier {Γ σ m} (h : OrdinalVector (σ :: Γ) m) : Nat :=
  2^(σ.level+1) * ((List.ofFn h).map ordinalPartialSize).sum

def copies (τ : Ty) : Nat := 2*(τ.level+1)
def coefficient (τ : Ty) : Nat := copies τ+1

structure Data where
  d : Nat
  d' : Nat
  free : Bool

def compile {Γ σ τ} (a : OriginalTerm (σ :: Γ) τ) : Option Data := do
  let h ← assignment OrdinalSyntax.defaultPolicy a
  let h' ← assignment OrdinalSyntax.defaultPolicy (unused a)
  pure ⟨multiplier h, multiplier h', ordinalHeadFree (h 0)⟩

def constant (τ : Ty) (d : Data) : Nat := 4*copies τ*d.d'+copies τ

/-- Unit observation is an admissible all-one vector substitution, NOT a
claimed source inhabitant. Every other closed vector is preserved exactly. -/
def unitExtension {Γ σ} (ρ : AdmissibleSubstitution Γ) : AdmissibleSubstitution (σ :: Γ) where
  vector := fun x j => match x with
    | .here => .one
    | .there y => ρ.vector y j
  graded := by
    intro τ x j
    cases x with
    | here => exact .one j.val
    | there y => exact ρ.graded y j
  bounded := by
    intro τ x j
    cases x with
    | here => exact le_rfl
    | there y => exact ρ.bounded y j

/-- Only scalar coordinates are natural observations. Higher coordinates of
remaining admissible vectors can be genuine ordinals. All sources share ρ. -/
def Observation {Γ τ} (ρ : AdmissibleSubstitution Γ) (a : OriginalTerm Γ τ) (n : Nat) : Prop :=
  ∃ v : OrdinalVector Γ τ.level,
    assignment OrdinalSyntax.defaultPolicy a = some v ∧ expressionValue ρ (v 0) = ((n+1 : Nat) : Ordinal)

/-- Compile-time branch and fixed positive coefficients; products are fixed
numeral multiples, hence finite addition expressions. Observation variables
l,l' are encoded natural values; r is the desired raw scalar. -/
def Formula {Γ σ τ} (ρ : AdmissibleSubstitution Γ) (a : OriginalTerm (σ :: Γ) τ)
    (d : Data) (r : Nat) : Prop :=
  if d.free then
    ∃ l : Nat, Observation ρ (first a) l ∧ l+1=(d.d+1)*r+d.d
  else
    ∃ l l' : Nat, Observation ρ (first a) l ∧ Observation ρ (second a) l' ∧
      coefficient τ*d.d'*(l+1)+d.d*constant τ d =
        d.d*(l'+1)+coefficient τ*(d.d'-d.d)*r

/-- The literal finite-copy scalar, before taking any partial or size. -/
def inflated {Γ} (τ : Ty) (t : OrdinalExpression Γ) : OrdinalExpression Γ :=
  .add (repeated OrdinalSyntax.defaultPolicy .scalarRepeat (copies τ) (.add t .one)) t

/-- The original selected-name observation, with all other components shared
through a genuine typed permutation. -/
noncomputable def selectedValuation {left right : List Ty} {σ : Ty}
    (ρ : AdmissibleSubstitution (left ++ right)) : OrdinalComponent (left ++ σ :: right) → Ordinal :=
  fun c => valuation (unitExtension (σ := σ) ρ)
    (ordinalComponentRename (SelectedBinder.moveToHead left right σ) c)
end LogicLineages.OrdinalComparison.Source.OneUnit
