module
public import LogicLineages.StandardControlCurrent.InverseCutSyntaxDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InverseCutSyntaxTargets
open OrdinalComparison LayeredComparison.SnyatkovCompletion InverseCutSyntax

def ParameterElimination : Prop := ∀ h m r x a b lo hi ν,
  x ∉ support a b lo hi →
  ((compile h m r a b lo hi).eval ν ↔ BoundCut h m r x a b lo hi ν)
def OutputSupport : Prop := ∀ h m r a b lo hi i,
  i ∈ (compile h m r a b lo hi).variables → i ∈ support a b lo hi
-- Freshness is about every occurrence, including syntactically inactive branches.
def UpdateAndNegation : Prop := ∀ h m r x a b lo hi ν,
  x ∉ support a b lo hi →
  (∀ n, (compile h m r a b lo hi).eval (Function.update ν x n) ↔
    (compile h m r a b lo hi).eval ν) ∧
  ((Matrix.negative (compile h m r a b lo hi)).eval ν ↔ ¬ BoundCut h m r x a b lo hi ν)
def LiteralCode : Prop := ∀ (h m r : Nat) (a b lo hi : Term),
  compileCode h m r a.encode b.encode lo.encode hi.encode = (compile h m r a b lo hi).encode

def Programs : Prop := Primrec program
def Invalid : Prop := ∀ h m r a b lo hi,
  (m = 0 ∨ m ≤ r) → compile h m r a b lo hi = .falsity

def Full : Prop := ParameterElimination ∧ OutputSupport ∧ UpdateAndNegation ∧ LiteralCode ∧ Programs ∧ Invalid
end LogicLineages.StandardControlCurrent.InverseCutSyntaxTargets
