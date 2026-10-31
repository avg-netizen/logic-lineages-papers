module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerAdjunctionDefinitions
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.PUnit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

/-- A presentation with its actual carrier and its named generators. -/
structure WalkerFinitePresentation (n : ℕ) where
  Carrier : Type
  group : AddCommGroup Carrier
  generator : Fin n → Carrier
attribute [instance] WalkerFinitePresentation.group

/-- A predecessor is either an earlier node or no node (a root). Thus cycles
are excluded by the type, not by an unproved presentation property. -/
abbrev WalkerParentSequence := (n : ℕ) → Option (Fin n)

def walkerFiniteExtension (p : ℕ) {n : ℕ} (S : WalkerFinitePresentation n)
    (parent : Option (Fin n)) : WalkerFinitePresentation (n+1) where
  Carrier := WalkerAdjunction p (parent.elim 0 S.generator)
  group := inferInstance
  generator := Fin.lastCases (walkerAdjunctionClass p (parent.elim 0 S.generator) 0 1)
    (fun i => walkerAdjunctionClass p (parent.elim 0 S.generator) (S.generator i) 0)

def walkerFinitePresentation (p : ℕ) (parent : WalkerParentSequence) :
    (n : ℕ) → WalkerFinitePresentation n
  | 0 => ⟨PUnit, inferInstance, Fin.elim0⟩
  | n+1 => walkerFiniteExtension p (walkerFinitePresentation p parent n) (parent n)

/-- Literal finite sum of the named generators, not an abstract digit field. -/
def walkerFiniteDigitSum (p : ℕ) (parent : WalkerParentSequence) (n : ℕ)
    (d : Fin n → Fin p) : (walkerFinitePresentation p parent n).Carrier :=
  ∑ i, (d i).val • (walkerFinitePresentation p parent n).generator i

end LogicLineages.ModelsAlgebra.PGroups
