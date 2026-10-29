module

public import LogicLineages.ComputabilityKnowledge.CircuitReduction

@[expose] public section

/-!
# Finite positive circuit comparison outputs

Paper02, displayed U,V and the comparison equivalences following its circuit
translation (lines 212–231). All inputs and auxiliaries are interpreted by ONE
finite positive valuation of size n+9*gateCount. Values outside that finite
range are defined as one only to evaluate the existing Nat-named syntax; the
independent target requires every actual variable to be inside the range.
Strict output orientation is (V,U); weak output orientation is (V+1,U).
This is not a polynomial front end, MRDP proof or admissible-vector bridge.
-/
namespace LogicLineages.ComputabilityKnowledge.CircuitComparison

open PositiveExpression CircuitReduction

def finiteVal {d : Nat} (ρ : Fin d → PosNat) : Nat → PosNat :=
  fun j => if h : j < d then ρ ⟨j,h⟩ else ⟨1, Nat.zero_lt_one⟩

def upper (c : Circuit) : Expr Nat := Comparators.ExponentialGap.systemLeft (compile c)
def lower (c : Circuit) : Expr Nat := Comparators.ExponentialGap.systemRight (compile c)
def weakLower (c : Circuit) : Expr Nat := .add (lower c) .one

def AgreesInputs (c : Circuit) (ρ : Fin c.inputCount → PosNat)
    (τ : Fin (variableBound c) → PosNat) : Prop :=
  ∀ j : Fin c.inputCount, finiteVal τ j.val = ρ j

def Solvable (c : Circuit) : Prop :=
  ∃ ρ : Fin c.inputCount → PosNat, c.outputEqual (finiteVal ρ)

/-- Header is the variable bound; the two term codes are length-framed by the
existing faithful System codec. Their order is the comparison's left/right. -/
def encodeComparison (p : Nat × Expr Nat × Expr Nat) : List Nat :=
  p.1 :: encodeSystem [(p.2.1,p.2.2)]

def strictOutput (c : Circuit) : Nat × Expr Nat × Expr Nat :=
  (variableBound c, lower c, upper c)

def weakOutput (c : Circuit) : Nat × Expr Nat × Expr Nat :=
  (variableBound c, weakLower c, upper c)

def strictCode (code : List Nat) : Option (List Nat) :=
  (decodeCircuit code).map (fun c => encodeComparison (strictOutput c))

def weakCode (code : List Nat) : Option (List Nat) :=
  (decodeCircuit code).map (fun c => encodeComparison (weakOutput c))

end LogicLineages.ComputabilityKnowledge.CircuitComparison
