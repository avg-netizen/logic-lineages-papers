module
public import LogicLineages.StandardControlCurrent.PolicyShapeTargets
public import Mathlib.Computability.PartrecCode

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedShape
open OrdinalComparison.Source.AdmissibleSum (Policy)
open Nat.Partrec (Code)

abbrev MacroArgs := Code × Nat × Nat × List Nat

/-- Correctness of a supplied program index is a semantic premise, not an
extra runtime input or an attempted totality test. -/
def Implements (code : Code) (p : Policy) : Prop :=
  ∀ (tag arity : Nat), Code.eval code (Nat.pair tag arity) =
    Part.some (Encodable.encode (PolicyShape.selector p tag arity))

def runTapeCode (operands : List Nat) (value : Nat) : Option Nat :=
  (Encodable.decode (α := List Bool) value).bind (fun tape => PolicyShape.expandCode tape operands)

/-- Outer partiality is a policy program that never returns. The inner
option is the actual macro result, including a returned failure. -/
noncomputable def macroCode (p : MacroArgs) : Part (Option Nat) :=
  (Code.eval p.1 (Nat.pair p.2.1 p.2.2.1)).map (runTapeCode p.2.2.2)

def ExactPolicyIndexedShape : Prop :=
  ∀ (c : Code) (p : Policy), Implements c p →
    ∀ (tag arity : Nat) (operands : List Nat),
      macroCode (c,tag,arity,operands) = Part.some (PolicyShape.macroCode p tag arity operands)

def ExactPolicyIndexedShapeValues : Prop :=
  ∀ (c : Code) (p : Policy), Implements c p →
    ∀ (tag arity : Nat) (operands : List Nat) (out : Option Nat),
      out ∈ macroCode (c,tag,arity,operands) ↔ out = PolicyShape.macroCode p tag arity operands

def ExactPolicyIndexedShapeDomain : Prop :=
  ∀ (p : MacroArgs), (macroCode p).Dom ↔ (Code.eval p.1 (Nat.pair p.2.1 p.2.2.1)).Dom

def EveryEffectivePolicyHasIndex : Prop :=
  ∀ p : Policy, PolicyShape.Effective p → ∃ c : Code, Implements c p

def FullPolicyIndexedShape : Prop :=
  Partrec macroCode ∧ ExactPolicyIndexedShape ∧ ExactPolicyIndexedShapeValues ∧
    ExactPolicyIndexedShapeDomain ∧ EveryEffectivePolicyHasIndex

end LogicLineages.StandardControlCurrent.PolicyIndexedShape
