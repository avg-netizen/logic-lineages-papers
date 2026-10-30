module

public import LogicLineages.OrdinalComparison.SourceFreeOccurrencesDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceFreeOccurrencesTargets
open SourceTypeSupport SourceFreeOccurrences

def FreeOccurrenceRenaming : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : List Ty) (τ : Ty)
    (t : Term Symbol arity Γ τ) (ρ : Renaming Γ Δ),
      freeOccurrences (t.rename ρ) = (freeOccurrences t).map (renamePacked ρ)

def OccurringVariableTypeSupport : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (τ : Ty)
    (t : Term Symbol arity Γ τ) (v : PackedVariable Γ),
      v ∈ freeOccurrences t → v.1 ∈ typeSupport t

def ImageTypeSupportMembership : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : List Ty)
    (s : Substitution Symbol arity Γ Δ) (vars : List (PackedVariable Γ)) (τ : Ty),
      τ ∈ imageTypeSupport s vars ↔ ∃ v ∈ vars, τ ∈ typeSupport (s v.2)

/-- The paper's displayed type-support equation on the actual typed kernel.
Named-source/marked comparison correspondence is not assumed. -/
def ExactTypeSupportSubstitution : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : List Ty) (τ : Ty)
    (t : Term Symbol arity Γ τ) (s : Substitution Symbol arity Γ Δ),
      typeSupport (t.substitute s) = typeSupport t ∪ imageTypeSupport s (freeOccurrences t)

/-- Free variables are replaced, unlike type support; no old-variable union. -/
def ExactFreeOccurrenceSubstitution : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : List Ty) (τ : Ty)
    (t : Term Symbol arity Γ τ) (s : Substitution Symbol arity Γ Δ),
      freeOccurrences (t.substitute s) =
        (freeOccurrences t).flatMap (fun v => freeOccurrences (s v.2))

end LogicLineages.OrdinalComparison.Source.SourceFreeOccurrencesTargets
