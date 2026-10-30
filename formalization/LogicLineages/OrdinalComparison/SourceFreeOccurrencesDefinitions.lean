module

public import LogicLineages.OrdinalComparison.SourceTypeSupportDefinitions

@[expose] public section
/-! Actual typed free-variable occurrences, retaining order and duplicates.
This is not type support: substitution replaces these occurrences, rather than
unconditionally retaining the old free variables. -/
namespace LogicLineages.OrdinalComparison.Source.SourceFreeOccurrences
open SourceTypeSupport

abbrev PackedVariable (Γ : List Ty) := Σ σ : Ty, Variable Γ σ

def renamePacked {Γ Δ : List Ty} (ρ : Renaming Γ Δ) : PackedVariable Γ → PackedVariable Δ
  | ⟨σ, v⟩ => ⟨σ, ρ v⟩

def dropBound {Γ : List Ty} {σ : Ty} : PackedVariable (σ :: Γ) → Option (PackedVariable Γ)
  | ⟨_, .here⟩ => none
  | ⟨τ, .there v⟩ => some ⟨τ, v⟩

def freeOccurrences {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (t : Term Symbol arity Γ τ) : List (PackedVariable Γ) :=
  match t with
  | .var v => [⟨_, v⟩]
  | .app f a => freeOccurrences f ++ freeOccurrences a
  | .lam body => (freeOccurrences body).filterMap dropBound
  | .zeroC | .succC | .caseC _ | .recC _ => []
  | .ranked s args => (List.ofFn (fun i : Fin (arity s) => freeOccurrences (args i))).flatten

def imageTypeSupport {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty}
    (s : Substitution Symbol arity Γ Δ) : List (PackedVariable Γ) → Finset Ty
  | [] => ∅
  | v :: rest => typeSupport (s v.2) ∪ imageTypeSupport s rest

end LogicLineages.OrdinalComparison.Source.SourceFreeOccurrences
