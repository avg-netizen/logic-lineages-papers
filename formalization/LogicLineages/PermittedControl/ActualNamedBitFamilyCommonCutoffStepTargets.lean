module
public import LogicLineages.PermittedControl.ActualNamedBitFamilyHighAboveTargets
public import LogicLineages.PermittedControl.ActualBitFamilyExistentialStepTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNamedBitFamilyCommonCutoffStep
open OrdinalComparison
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyLowSlices (strips dimension)
open ActualBitFamilyExistentialLow (Satisfiable closed)
open ActualBitFamilyExistentialStep (Layer LayerHolds)
open ActualNamedBitFamilyHigh (Supplied cutoff)
open ActualNamedBitFamilyHighAbove (compile)

noncomputable def low (f : Nat → Nat) (C : Nat) (family : Family) (names : List Nat) : List Family :=
  names.flatMap (fun name => (strips f name C family).map Prod.snd)

noncomputable def children (f : Nat → Nat) (C : Nat) (family : Family) (names : List Nat) : List Family :=
  low f C family names ++ (compile C family names).map Prod.snd

noncomputable def layer (f : Nat → Nat) (C : Nat) (family : Family) (names : List Nat) : Layer :=
  if dimension family = 0 then .closed (closed family) else .descend (children f C family names)

def ExactNamedLowChildMembership : Prop :=
  ∀ (f : Nat → Nat) (C : Nat) (family : Family) (names : List Nat), Supplied family names →
    ∀ out : Family, out ∈ low f C family names ↔ out ∈ ActualBitFamilyExistentialLow.children f C family

def ExactCommonCutoffNonemptyStep : Prop :=
  ∀ (f : Nat → Nat) (B C : Nat), SelectedWithThreshold f B →
    ∀ (family : Family) (names : List Nat), Supplied family names → cutoff B family names ≤ C →
      0 < dimension family →
        (Satisfiable f family ↔ ∃ out ∈ children f C family names, Satisfiable f out)

def ExactCommonCutoffChildrenSmaller : Prop :=
  ∀ (f : Nat → Nat) (C : Nat) (family : Family) (names : List Nat), Supplied family names →
    ∀ out ∈ children f C family names, dimension out < dimension family

def ExactCommonCutoffLayer : Prop :=
  ∀ (f : Nat → Nat) (B C : Nat), SelectedWithThreshold f B →
    ∀ (family : Family) (names : List Nat), Supplied family names → cutoff B family names ≤ C →
      (LayerHolds f (layer f C family names) ↔ Satisfiable f family)

def FullActualNamedBitFamilyCommonCutoffStep : Prop :=
  ExactNamedLowChildMembership ∧ ExactCommonCutoffNonemptyStep ∧
    ExactCommonCutoffChildrenSmaller ∧ ExactCommonCutoffLayer

end LogicLineages.PermittedControl.ActualNamedBitFamilyCommonCutoffStep
