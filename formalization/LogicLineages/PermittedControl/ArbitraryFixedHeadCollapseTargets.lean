module
public import LogicLineages.PermittedControl.FixedHeadCollapseGraphTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ArbitraryFixedHeadCollapse
open OrdinalComparison

abbrev Input := FixedHeadCollapseGraph.Input

/-- Move the original finite tail and the new input to the raw norm
coordinate of the actual decoded limit part. -/
def transported (p : Input) : FixedHeadCollapseGraph.Input :=
  let split := (rawSplitCode p.1).unpair
  (split.1,rawNormCode split.1 + (split.2 + p.2))

noncomputable def read (f : Nat → Nat) (p : Input) : Option Nat :=
  if rawNormalCode p.1 = 1 then
    if encodedFiniteTest p.1 then some (encodedFiniteValue p.1 + p.2)
    else FixedHeadCollapseGraph.read f (transported p)
  else none

def ActualNormalization : Prop :=
  ∀ p : Input, ONote.NF (rawNoteDecode p.1) →
    let a := (rawNoteDecode p.1).repr
    (encodedFiniteTest p.1 = true ↔ a < Ordinal.omega0) ∧
    (encodedFiniteTest p.1 = true → a = (encodedFiniteValue p.1 : Ordinal)) ∧
    (Ordinal.omega0 ≤ a →
      let q := transported p
      let lam := (rawNoteDecode q.1).repr
      FixedHeadCollapseGraph.domain q ∧ lam = actualLimitPart a ∧
      (rawSplitCode p.1).unpair.2 = actualTailPart a ∧
      q.2 = actualOrdinalNorm lam + (actualTailPart a + p.2) ∧
      countInitial lam q.2 = a + (p.2 : Ordinal))

def Effectivity : Prop :=
  Primrec transported ∧ ∀ f : Nat → Nat, Computable f → Computable (read f)

def ActualGraph : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ p : Input,
    let a := (rawNoteDecode p.1).repr
    (read f p = none ↔ ¬ ONote.NF (rawNoteDecode p.1)) ∧
    (∀ y : Nat, read f p = some y ↔ ONote.NF (rawNoteDecode p.1) ∧
      y = ParametricActualCollapse.collapseWith f (a + (p.2 : Ordinal)))

def FullArbitraryFixedHeadCollapse : Prop :=
  ActualNormalization ∧ Effectivity ∧ ActualGraph

end LogicLineages.PermittedControl.ArbitraryFixedHeadCollapse
