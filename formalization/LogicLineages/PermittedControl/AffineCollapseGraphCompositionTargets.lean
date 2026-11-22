module
public import LogicLineages.PermittedControl.NaturalAffineGateGraphTargets
public import LogicLineages.PermittedControl.FixedHeadCollapseGraphTargets

@[expose] public section
namespace LogicLineages.PermittedControl.AffineCollapseGraphComposition
open OrdinalComparison

abbrev Expression := NaturalAffineGateGraph.Expression

def Fresh (e : Expression) (inputName outputName : Nat) : Prop :=
  inputName ≠ outputName ∧
    ∀ occurrence ∈ e.2, occurrence.2 ≠ inputName ∧ occurrence.2 ≠ outputName

def insertValues (ν : Nat → Nat) (inputName outputName : Nat) (values : Nat × Nat) :
    Nat → Nat :=
  Function.update (Function.update ν inputName values.1) outputName values.2

def graph (f : Nat → Nat) (head : Nat) (e : Expression) (inputName outputName : Nat)
    (θ : Nat → Nat) : Prop :=
  (NaturalAffineGateGraph.graph inputName e).eval θ ∧
    FixedHeadCollapseGraph.read f (head,θ inputName) = some (θ outputName)

/-- The affine output must be natural before its actual use as an
unshifted raw norm input at the original fixed head. -/
def originalDomain (head : Nat) (e : Expression) (ν : Nat → Nat) : Prop :=
  let s := NaturalAffineGateGraph.signedValue e ν
  0 ≤ s ∧ FixedHeadCollapseGraph.domain (head,s.toNat)

noncomputable def originalValues (f : Nat → Nat) (head : Nat) (e : Expression) (ν : Nat → Nat) :
    Nat × Nat :=
  let t := (NaturalAffineGateGraph.signedValue e ν).toNat
  (t,headCollapse f (rawNoteDecode head).repr t)

def ExactPairExtension : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (head : Nat) (e : Expression) (inputName outputName : Nat) (ν : Nat → Nat),
    Fresh e inputName outputName →
    (∀ values : Nat × Nat,
      graph f head e inputName outputName (insertValues ν inputName outputName values) ↔
        originalDomain head e ν ∧ values = originalValues f head e ν) ∧
    ((∃! values : Nat × Nat,
      graph f head e inputName outputName (insertValues ν inputName outputName values)) ↔
        originalDomain head e ν) ∧
    (∀ (values : Nat × Nat) (name : Nat), name ≠ inputName → name ≠ outputName →
      insertValues ν inputName outputName values name = ν name)

def ExactTestPolarity : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (head : Nat) (e : Expression) (inputName outputName : Nat) (ν : Nat → Nat),
    Fresh e inputName outputName → ∀ test : (Nat → Nat) → Prop,
    let correct := insertValues ν inputName outputName (originalValues f head e ν)
    ((∃ values : Nat × Nat,
      let θ := insertValues ν inputName outputName values
      graph f head e inputName outputName θ ∧ test θ) ↔
        originalDomain head e ν ∧ test correct) ∧
    ((∃ values : Nat × Nat,
      let θ := insertValues ν inputName outputName values
      graph f head e inputName outputName θ ∧ ¬ test θ) ↔
        originalDomain head e ν ∧ ¬ test correct)

def FullAffineCollapseGraphComposition : Prop := ExactPairExtension ∧ ExactTestPolarity

end LogicLineages.PermittedControl.AffineCollapseGraphComposition
