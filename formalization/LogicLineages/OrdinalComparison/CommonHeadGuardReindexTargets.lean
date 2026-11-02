module
public import LogicLineages.OrdinalComparison.CommonHeadGuardReindexDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadGuardReindex.Targets
open CommonHeadLargeRow CommonHeadLargeGuards

/-- Exact syntax support and evaluation under any shared-index renaming. -/
def ExactRenaming : Prop := ∀ (σ : Nat → Nat) (p : Formula),
  (rename σ p).variables=p.variables.map σ ∧
  ∀ ν, (rename σ p).eval ν ↔ p.eval (ν ∘ σ)

/-- Delete precisely one coefficient/input occurrence and restore its original
labels on the shorter row. No permutation of surviving occurrences is hidden. -/
def ExactDeletion : Prop := ∀ (cs : List Int) (i : Fin cs.length) (ν : Nat → Nat),
  inputRow (cs.eraseIdx i.val) (ν ∘ skip i.val)=(inputRow cs ν).eraseIdx i.val ∧
  ∀ j<(cs.eraseIdx i.val).length, skip i.val j<cs.length ∧ skip i.val j≠i.val

/-- The small guard fixes the complete actual argument before folding its
closed value. The recursive child may use only its surviving input indices. -/
def ExactGuardedFold : Prop := ∀ (lam : Ordinal) (K : Int) (cs : List Int)
  (i : Fin cs.length) (c : Nat) (p : Formula),
  (∀ j∈p.variables, j<(cs.eraseIdx i.val).length) →
  (∀ j∈(guarded i.val c p).variables, j<cs.length) ∧
  ∀ ν : Nat → Nat,
    ((guarded i.val c p).eval ν ↔ ν i.val=c ∧ p.eval (ν ∘ skip i.val)) ∧
    (ν i.val=c →
      value lam (K+cs[i]*(actualHeadValue lam c : Int))
        (inputRow (cs.eraseIdx i.val) (ν ∘ skip i.val)) = value lam K (inputRow cs ν))
end LogicLineages.OrdinalComparison.CommonHeadGuardReindex.Targets
