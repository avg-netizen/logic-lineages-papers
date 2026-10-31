module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerOrdinalNodeDefinitions
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

def walkerPresentationRelation {V : Type} (p : ℕ) (parent : V → Option V) (v : V) :
    FreeAbelianGroup V :=
  p • FreeAbelianGroup.of v - (parent v).elim 0 FreeAbelianGroup.of

def walkerPresentationRelations {V : Type} (p : ℕ) (parent : V → Option V) :
    AddSubgroup (FreeAbelianGroup V) :=
  AddSubgroup.closure (Set.range (walkerPresentationRelation p parent))

/-- Literal free-abelian group presentation, rather than an interface carrying
normal form, filtration, or a universal-property assumption. -/
abbrev WalkerPresentedGroup {V : Type} (p : ℕ) (parent : V → Option V) :=
  FreeAbelianGroup V ⧸ walkerPresentationRelations p parent

def walkerPresentedGenerator {V : Type} (p : ℕ) (parent : V → Option V) (v : V) :
    WalkerPresentedGroup p parent := QuotientAddGroup.mk (FreeAbelianGroup.of v)

/-- The original source Walker group on every decreasing-ordinal node. -/
abbrev WalkerSourceGroup (p : ℕ) (ξ : Ordinal.{0}) :=
  WalkerPresentedGroup p (walkerOrdinalParent ξ)

end LogicLineages.ModelsAlgebra.PGroups
