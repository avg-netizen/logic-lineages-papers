module
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.RankResidueChoices

/-- The positive table name followed by its actual raw rank. -/
abbrev Slot := Nat × Nat
/-- The same name and rank with a selected raw residue. -/
abbrev Digit := Nat × Nat × Nat
abbrev Cell := List Digit

def namedSlots (ranks : List Nat) : List Slot :=
  (List.range ranks.length).map (fun i => (i+1,ranks[i]?.getD 0))

def extend (m : Nat) (slot : Slot) (cells : List Cell) : List Cell :=
  (List.range (2*m)).flatMap (fun j => cells.map (fun cell => (slot.1,slot.2,j) :: cell))

def choices (m : Nat) (slots : List Slot) : List Cell :=
  slots.foldr (extend m) [[]]

inductive Assignment (bound : Nat) : List Slot → Cell → Prop where
  | nil : Assignment bound [] []
  | cons {s : Slot} {j : Nat} {slots : List Slot} {cell : Cell} :
      j < bound → Assignment bound slots cell → Assignment bound (s :: slots) ((s.1,s.2,j) :: cell)

def actualCell (m : Nat) (slots : List Slot) (ρ : Nat → Nat) : Cell :=
  slots.map (fun s => (s.1,s.2,ρ s.2 % (2*m)))

def LayoutAndChoices : Prop :=
  Primrec namedSlots ∧ Primrec₂ choices ∧
  (∀ ranks : List Nat, (namedSlots ranks).map Prod.snd = ranks ∧
    (namedSlots ranks).map Prod.fst = (List.range ranks.length).map Nat.succ) ∧
  (∀ (m : Nat) (slots : List Slot) (cell : Cell),
    cell ∈ choices m slots ↔ Assignment (2*m) slots cell) ∧
  ∀ (m : Nat) (slots : List Slot) (ρ : Nat → Nat), 0 < m → actualCell m slots ρ ∈ choices m slots

end LogicLineages.PermittedControl.RankResidueChoices
