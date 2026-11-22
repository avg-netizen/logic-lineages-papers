module
public import LogicLineages.PermittedControl.ClosedOrdinaryFieldTargets

@[expose] public section
namespace LogicLineages.PermittedControl.FixedHeadCollapseGraph
open OrdinalComparison FieldComparison

abbrev Input := Nat × Nat

def domain (p : Input) : Prop :=
  let lam := rawNoteDecode p.1
  ONote.NF lam ∧ Order.IsSuccLimit lam.repr ∧ actualOrdinalNorm lam.repr ≤ p.2

def guard (p : Input) : Bool :=
  closedProperEntryGuard (p.1,0,p.2)

/-- The two fields live at the same original initial state, with zero
as the fixed terminal target of the retained closed entry evaluator. -/
noncomputable def fields (f : Nat → Nat) (p : Input) : Option (Nat × Nat) :=
  (closedProperEntryResult f (p.1,0,p.2)).join

noncomputable def read (f : Nat → Nat) (p : Input) : Option Nat :=
  (fields f p).map (fun hit => hit.1 + hit.2)

def GuardExact : Prop :=
  Primrec guard ∧ ∀ p : Input, guard p = true ↔ domain p

def GraphEffective : Prop :=
  ∀ (f : Nat → Nat), Computable f → Computable (fields f) ∧ Computable (read f)

def ExactTerminalFields : Prop :=
  ∀ (f : Nat → Nat) (p : Input),
    let lam := (rawNoteDecode p.1).repr
    (fields f p = none ↔ ¬ domain p) ∧
    (domain p → fields f p = some (completeEndpoint f lam p.2,completeCount f lam p.2))

def ExactSourceGraph : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (p : Input),
    let lam := (rawNoteDecode p.1).repr
    (∀ y : Nat, read f p = some y ↔ domain p ∧ y = headCollapse f lam p.2) ∧
    ((∃! y : Nat, read f p = some y) ↔ domain p) ∧
    (∀ test : Nat → Prop,
      (∃ y : Nat, read f p = some y ∧ ¬ test y) ↔
        domain p ∧ ¬ test (headCollapse f lam p.2))

def FullFixedHeadCollapseGraph : Prop :=
  GuardExact ∧ GraphEffective ∧ ExactTerminalFields ∧ ExactSourceGraph

end LogicLineages.PermittedControl.FixedHeadCollapseGraph
