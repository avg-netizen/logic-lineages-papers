module
public import LogicLineages.StandardControlCurrent.MixedRunnerBlockDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.MixedRunnerBlockTargets
open OrdinalComparison LayeredComparison.SnyatkovCompletion MixedRunnerBlock

/-- Includes actual low-end recovery, not only closeness of numerical outputs. -/
def ReverseWitness : Prop := ∀ i anchor e c ν,
  (ReverseWindow.closeMatrix i anchor e c).eval ν →
  ∃ d : Nat, d ≤ c ∧
    anchor.value ν = (shiftTerm (.variable i) e).value ν+d ∧
    (ReverseWindow.replacementTerm anchor e d).value ν=ν i

def ReverseElimination : Prop := ∀ i anchor e c p,
  i ∉ anchor.variables → ∀ ν,
  ((∃ n : Nat, (Matrix.conjunction (ReverseWindow.closeMatrix i anchor e c) p).eval
    (Function.update ν i n)) ↔ (ReverseWindow.finiteCases i anchor e c p).eval ν)
def ReverseBlock : Prop := ∀ xs i anchor e c p,
  i ∉ anchor.variables → Reduction xs i
    (.conjunction (ReverseWindow.closeMatrix i anchor e c) p)
    (ReverseWindow.finiteCases i anchor e c p)

def LinearBounds : Prop :=
  (∀ kind e h a n,
    (LinearWindow.valueTerm 0 kind e h).value (fun _ => n) ≤ a*n →
    n < LinearWindow.bound kind e h a) ∧
  (∀ i j leftKind rightKind e h k l a ν,
    (LinearWindow.guard i j leftKind rightKind e h k l a).eval ν →
    ν j < LinearWindow.bound rightKind k l a)
/-- Distinct-name restriction explicit: no same-name coverage claimed here. -/
def LinearElimination : Prop := ∀ i j, i ≠ j → ∀ leftKind rightKind e h k l a p ν,
  ((∃ n : Nat, (Matrix.conjunction (LinearWindow.guard i j leftKind rightKind e h k l a) p).eval
    (Function.update ν j n)) ↔ (LinearWindow.finiteCases i j leftKind rightKind e h k l a p).eval ν)
def LinearBlock : Prop := ∀ xs i j, i ≠ j → ∀ leftKind rightKind e h k l a p,
  Reduction xs j (.conjunction (LinearWindow.guard i j leftKind rightKind e h k l a) p)
    (LinearWindow.finiteCases i j leftKind rightKind e h k l a p)

def ActiveBounds : Prop :=
  (∀ e h k a n,
    LayeredComparison.SnyatkovHyperCollision.translatedValue (((n : Int)+e).toNat) h ≤
      a*Phi (((n : Int)+k).toNat) → n < ActiveHyper.bound e h k a) ∧
  (∀ i j kind e h k l q a ν,
    (ActiveHyper.guard i j kind e h k l q a).eval ν → ν j < ActiveHyper.bound k l q a)
/-- Unlike LinearElimination, identical names i=j are included. -/
def ActiveElimination : Prop := ∀ i j kind e h k l q a p ν,
  ((∃ n : Nat, (Matrix.conjunction (ActiveHyper.guard i j kind e h k l q a) p).eval
    (Function.update ν j n)) ↔ (ActiveHyper.finiteCases i j kind e h k l q a p).eval ν)
def ActiveBlock : Prop := ∀ xs i j kind e h k l q a p,
  Reduction xs j (.conjunction (ActiveHyper.guard i j kind e h k l q a) p)
    (ActiveHyper.finiteCases i j kind e h k l q a p)

def LiteralCode : Prop :=
  (∀ xs i anchor e c p,
    reverseProgram (xs,ReverseWindow.Code.input i anchor.encode e c p.encode)=
      (xs.erase i,(ReverseWindow.finiteCases i anchor e c p).encode)) ∧
  (∀ xs i j lk rk e h k l a p,
    linearProgram (xs,LinearWindow.Code.input i j lk rk e h k l a p.encode)=
      (xs.erase j,(LinearWindow.finiteCases i j lk rk e h k l a p).encode)) ∧
  (∀ xs i j kind e h k l q a p,
    activeProgram (xs,ActiveHyper.Code.input i j kind e h k l q a p.encode)=
      (xs.erase j,(ActiveHyper.finiteCases i j kind e h k l q a p).encode))
def Programs : Prop :=
  Primrec (fun p : Bool × (Int × (Int × Nat)) => LinearWindow.bound p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Int × (Int × (Int × Nat)) => ActiveHyper.bound p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Computable reverseProgram ∧ Computable linearProgram ∧ Computable activeProgram

def Full : Prop := ReverseWitness ∧ ReverseElimination ∧ ReverseBlock ∧
  LinearBounds ∧ LinearElimination ∧ LinearBlock ∧ ActiveBounds ∧
  ActiveElimination ∧ ActiveBlock ∧ LiteralCode ∧ Programs
end LogicLineages.StandardControlCurrent.MixedRunnerBlockTargets
