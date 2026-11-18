module
public import LogicLineages.StandardControlCurrent.HyperCloseBlockDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.HyperCloseBlockTargets
open OrdinalComparison LayeredComparison.SnyatkovCompletion HyperCloseBlock

def ActualAlternatives : Prop := ∀ i j e h k l c ν,
  (HyperWindow.closeMatrix i j e h k l c).eval ν →
  ν i < HyperWindow.leftBound e h l ∨ ν j < HyperWindow.rightBound h k l c ∨
    (HyperWindow.indexTerm i e).value ν = (HyperWindow.indexTerm j k).value ν

def PairElimination : Prop := ∀ i j, i ≠ j → ∀ e h k l c p ν,
  (∃ x y : Nat, (Matrix.conjunction (HyperWindow.closeMatrix i j e h k l c) p).eval
    (Function.update (Function.update ν i x) j y)) ↔
  (∃ y : Nat, (HyperWindow.leftCases i j e h k l c p).eval (Function.update ν j y)) ∨
  (∃ x : Nat, (HyperWindow.rightCases i j e h k l c p).eval (Function.update ν i x)) ∨
  (∃ y : Nat, (HyperWindow.equalCases i j e h k l c p).eval (Function.update ν j y))

def BlockPermutation : Prop := ∀ (xs ys : List Nat) (p : Matrix) (ν : Nat → Nat),
  xs.Nodup → xs.Perm ys → (existsNames xs p ν ↔ existsNames ys p ν)
def BlockElimination : Prop := ∀ (xs : List Nat) i j e h k l c p ν,
  xs.Nodup → i ∈ xs → j ∈ xs → i ≠ j →
  (existsNames xs (.conjunction (HyperWindow.closeMatrix i j e h k l c) p) ν ↔
    result (branches xs i j e h k l c p) ν)
def StrictDecrease : Prop := ∀ (xs : List Nat) i j e h k l c p,
  xs.Nodup → i ∈ xs → j ∈ xs → i ≠ j →
  ∀ b ∈ branches xs i j e h k l c p,
    b.1.Nodup ∧ b.1.length+1=xs.length ∧ b.1.length<xs.length ∧
    ∀ name, name ∈ b.2.variables → name ∉ b.1 → name ∈ p.variables ∧ name ∉ xs

def LiteralCode : Prop := ∀ xs i j e h k l c p,
  program (xs,HyperWindowCode.input i j e h k l c p.encode) =
    (branches xs i j e h k l c p).map (fun b => (b.1,b.2.encode))
def Programs : Prop :=
  Primrec (fun q : Int × Int × Int => HyperWindow.leftBound q.1 q.2.1 q.2.2) ∧
  Primrec (fun q : Int × Int × Int × Nat => HyperWindow.rightBound q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
  Computable program

def Full : Prop := ActualAlternatives ∧ PairElimination ∧ BlockPermutation ∧
  BlockElimination ∧ StrictDecrease ∧ LiteralCode ∧ Programs
end LogicLineages.StandardControlCurrent.HyperCloseBlockTargets
