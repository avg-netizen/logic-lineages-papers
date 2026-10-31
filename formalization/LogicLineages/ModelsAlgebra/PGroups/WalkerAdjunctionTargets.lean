module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerAdjunctionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Unique p-digit representatives of the literal root-adjunction quotient.
This is the source's one-leaf finite-tree step, not the entire Walker lemma. -/
def walkerAdjunctionUniqueDigits : Prop :=
  ∀ (H : Type) [AddCommGroup H] (p : ℕ), 0 < p → ∀ a : H,
    ∀ x : WalkerAdjunction p a,
      ∃! d : H × ℤ, 0 ≤ d.2 ∧ d.2 < (p : ℤ) ∧
        walkerAdjunctionClass p a d.1 d.2 = x

def walkerAdjunctionFaithful : Prop :=
  ∀ (H : Type) [AddCommGroup H] (p : ℕ), 0 < p → ∀ a : H,
    Function.Injective (fun h : H => walkerAdjunctionClass p a h 0)

def walkerAdjunctionRootRelation : Prop :=
  ∀ (H : Type) [AddCommGroup H] (p : ℕ) (a : H),
    p • walkerAdjunctionClass p a 0 1 = walkerAdjunctionClass p a a 0

end LogicLineages.ModelsAlgebra.PGroups.Targets
