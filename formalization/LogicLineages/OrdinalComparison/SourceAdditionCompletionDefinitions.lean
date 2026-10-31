module
public import LogicLineages.OrdinalComparison.SourceSortCompletionDefinitions
public import Mathlib.Data.Nat.BinaryRec
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAdditionCompletion
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open SourceSortCompletion

/-- Ground leaves used by the literal addition gadgets. -/
inductive Atom (Γ : List Ty) where
  | zero : Atom Γ
  | var : Variable Γ .ground → Atom Γ

def Atom.term {Γ} : Atom Γ → OriginalTerm Γ .ground
  | .zero => .zeroC
  | .var x => .var x

/-- Actual unused-binder eraser. Typed weakening makes the new de-Bruijn head
fresh and prevents capture; no beta reduction is performed. -/
def eraser {Γ} (a b : Atom Γ) : OriginalTerm Γ .ground :=
  .app (.lam (a.term.rename (Renaming.weaken Γ .ground))) b.term

def Equation {Γ} (ρ : OrdinalComponent Γ → Nat)
    (a b : OriginalTerm Γ .ground) : Prop :=
  ∃ va vb : OrdinalVector Γ 0,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a = some va ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy b = some vb ∧
    denote (fun c => ((ρ c + 1 : Nat) : Ordinal)) (va 0) =
      denote (fun c => ((ρ c + 1 : Nat) : Ordinal)) (vb 0)

/-- One fresh witness; every original component retains exactly its value. -/
def extend {Γ} (ρ : OrdinalComponent Γ → Nat) (d : Nat) :
    OrdinalComponent (.ground :: Γ) → Nat
  | ⟨_, .here, _⟩ => d
  | ⟨_, .there x, j⟩ => ρ ⟨_, x, j⟩

def AddWitness {Γ} (ρ : OrdinalComponent Γ → Nat)
    (a b c : Variable Γ .ground) (d : Nat) : Prop :=
  Equation (extend ρ d) (eraser (.var (.there b)) .zero)
    (eraser .zero (.var .here)) ∧
  Equation (extend ρ d) (eraser (.var (.there a)) (.var .here))
    (eraser (.var (.there c)) .zero)

def AddFormula {Γ} (ρ : OrdinalComponent Γ → Nat)
    (a b c : Variable Γ .ground) : Prop := ∃ d, AddWitness ρ a b c d

def identity {Γ} : OriginalTerm Γ (.arrow .ground .ground) := .lam (.var .here)

def singletonVal (u : Nat) : OrdinalComponent [.ground] → Nat := fun _ => u

/-- Constant-size definition: one S/I equation and the two addition equations.
The two inputs of Add are literally the same old variable, not split names. -/
def OneFormula (u : Nat) : Prop := ∃ v : Nat,
  Equation (extend (singletonVal u) v) (successorProbe .here) (.app identity .zeroC) ∧
  AddFormula (extend (singletonVal u) v) (.there .here) (.there .here) .here

/-- Ports are evaluated by one fixed valuation; repeating a numeric wire
never produces independently quantified copies of that wire. -/
def tripleVal (a b c : Nat) : OrdinalComponent [.ground, .ground, .ground] → Nat :=
  extend (extend (singletonVal c) b) a

def AddValues (a b c : Nat) : Prop :=
  AddFormula (tripleVal a b c) .here (.there .here) (.there (.there .here))

/-- A shared predecessor appears once in the syntax. `doubleOne` expands to
two addition gates, and `double` feeds one wire into both input ports. -/
inductive BinaryDAG where
  | zero | one
  | double : BinaryDAG → BinaryDAG
  | doubleOne : BinaryDAG → BinaryDAG

def BinaryDAG.gates : BinaryDAG → Nat
  | .zero | .one => 0
  | .double p => p.gates + 1
  | .doubleOne p => p.gates + 2

/-- Finite existential/conjunctive graph built only from the paid source
addition formula; base zero and one are supplied as in the manuscript. -/
def BinaryDAG.Run : BinaryDAG → Nat → Prop
  | .zero, y => y = 0
  | .one, y => y = 1
  | .double p, y => ∃ x, p.Run x ∧ AddValues x x y
  | .doubleOne p, y => ∃ x z, p.Run x ∧ AddValues x x z ∧ AddValues z 1 y

def binaryDAG (k : Nat) : BinaryDAG :=
  if h : k < 2 then if k = 0 then .zero else .one
  else if k % 2 = 0 then .double (binaryDAG (k / 2))
  else .doubleOne (binaryDAG (k / 2))
termination_by k
decreasing_by all_goals exact Nat.div_lt_self (by omega) (by omega)
end LogicLineages.OrdinalComparison.Source.SourceAdditionCompletion
