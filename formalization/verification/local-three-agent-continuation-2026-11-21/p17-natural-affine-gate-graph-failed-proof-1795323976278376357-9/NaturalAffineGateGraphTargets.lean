module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.NaturalAffineGateGraph
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

abbrev Input := Int × Nat
abbrev Expression := Int × List Input

def signedValue (e : Expression) (ν : Nat → Nat) : Int :=
  e.1 + (e.2.map (fun t => t.1 * (ν t.2 : Int))).sum

def lowerRow (output : Nat) (e : Expression) : NormalForm.Row :=
  (e.1,(-1,.variable output) :: e.2.map (fun t => (t.1,.variable t.2)))

def upperRow (output : Nat) (e : Expression) : NormalForm.Row :=
  (-e.1,(1,.variable output) :: e.2.map (fun t => (-t.1,.variable t.2)))

def graph (output : Nat) (e : Expression) : NormalForm.Formula :=
  .conjunction (.atom (.nonnegative (lowerRow output e))) (.atom (.nonnegative (upperRow output e)))

def lowerData (output : Nat) (e : Expression) : NormalForm.Code.AtomData :=
  (0,0,e.1,(-1,(0,output,0,0)) :: e.2.map (fun t => (t.1,(0,t.2,0,0))))

def upperData (output : Nat) (e : Expression) : NormalForm.Code.AtomData :=
  (0,0,-e.1,(1,(0,output,0,0)) :: e.2.map (fun t => (-t.1,(0,t.2,0,0))))

def graphCode (output : Nat) (e : Expression) : Nat :=
  6 * Nat.pair (6 * Encodable.encode (lowerData output e) + 2)
    (6 * Encodable.encode (upperData output e) + 2) + 4

def CodeExact : Prop := Primrec₂ graphCode ∧ ∀ (output : Nat) (e : Expression), graphCode output e = (graph output e).encode

def SignedGraph : Prop := ∀ (output : Nat) (e : Expression) (ν : Nat → Nat),
  (graph output e).eval ν ↔ (ν output : Int) = signedValue e ν

/-- Updating a fresh natural output cannot change any actual gate input.
A natural graph extension exists precisely on the source domain. -/
def ActualNaturalExtension : Prop :=
  ∀ (output : Nat) (e : Expression) (ν : Nat → Nat),
    (∀ t ∈ e.2, t.2 ≠ output) →
    (∀ y : Nat, (graph output e).eval (Function.update ν output y) ↔ (y : Int) = signedValue e ν) ∧
    ((∃! y : Nat, (graph output e).eval (Function.update ν output y)) ↔ 0 ≤ signedValue e ν) ∧
    ∀ (y name : Nat), name ≠ output → Function.update ν output y name = ν name

def FullNaturalAffineGateGraph : Prop := CodeExact ∧ SignedGraph ∧ ActualNaturalExtension

end LogicLineages.PermittedControl.NaturalAffineGateGraph
