module
public import LogicLineages.PermittedControl.ActualBitFamilyExistentialLowTargets
public import LogicLineages.PermittedControl.ActualBitFamilyHighTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyExistentialStep
open OrdinalComparison
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyExistentialLow (Satisfiable)
open ActualBitFamilyLowSlices (dimension)
open ActualBitFamilyHigh (cutoff compile)

noncomputable def children (f : Nat → Nat) (B : Nat) (family : Family) : List Family :=
  ActualBitFamilyExistentialLow.children f (cutoff B family) family ++
    (compile B family).map Prod.snd

def ExactNonemptyBitFamilyStep : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ family : Family, 0 < dimension family →
      (Satisfiable f family ↔ ∃ out ∈ children f B family, Satisfiable f out)

def ExactSmallerBitFamilyChildren : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (family : Family), ∀ out ∈ children f B family,
    dimension out < dimension family

inductive Layer where
  | closed (reply : Bool)
  | descend (children : List Family)

/-- A single exact generic round; cutoff high and low share the same
source support split. The children are in the same typed input family. -/
noncomputable def layer (f : Nat → Nat) (B : Nat) (family : Family) : Layer :=
  if dimension family = 0 then .closed (ActualBitFamilyExistentialLow.closed family)
  else .descend (children f B family)

def LayerHolds (f : Nat → Nat) : Layer → Prop
  | .closed b => b = true
  | .descend children => ∃ out ∈ children, Satisfiable f out

def ExactSoundBitFamilyLayer : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ family : Family, (LayerHolds f (layer f B family) ↔ Satisfiable f family)

def FullActualBitFamilyExistentialStep : Prop :=
  ExactNonemptyBitFamilyStep ∧ ExactSmallerBitFamilyChildren ∧ ExactSoundBitFamilyLayer

end LogicLineages.PermittedControl.ActualBitFamilyExistentialStep
