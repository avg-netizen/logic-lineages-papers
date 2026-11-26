module
public import LogicLineages.StandardControlCurrent.PolicyShapeDefinitions
public import Mathlib.Computability.PartrecCode

@[expose] public section
namespace LogicLineages.PermittedControl.PolicySuppliedCodeMacro
open OrdinalComparison.Source.AdmissibleSum
open StandardControlCurrent

/-- The actual supplied ordinary program computes the existing policy's
literal shape script at every macro site and arity. This specifies the
input program, without replacing the policy or assuming a compiler result. -/
def RealizesPolicy (e : Nat.Partrec.Code) (p : Policy) : Prop :=
  ∀ tag n : Nat, e.eval (Nat.pair tag n) =
    Part.some (Encodable.encode (PolicyShape.selector p tag n))

/-- Decode the returned script and run the existing literal expansion.
A malformed script encoding or a rejected expansion remains `none`. -/
def decodeExpand (z : Nat) (xs : List Nat) : Option Nat :=
  (Encodable.decode z : Option (List Bool)).bind
    (fun script => PolicyShape.expandCode script xs)

abbrev Args := Nat.Partrec.Code × Nat × Nat × List Nat

/-- One ordinary evaluator for every supplied policy program. The outer
`Part` preserves divergence of a supplied program; the inner `Option`
preserves the existing syntactic rejection. No totality on arbitrary
program codes is imposed. -/
noncomputable def macroEval (a : Args) : Part (Option Nat) :=
  (a.1.eval (Nat.pair a.2.1 a.2.2.1)).map
    (fun z => decodeExpand z a.2.2.2)

/-- Joint partial recursiveness in the supplied code and all raw arguments. -/
def MacroPartrec : Prop := Partrec macroEval

/-- On any supplied program realizing the policy selector, this evaluator
terminates and returns exactly the existing macro expansion, including its
possible syntactic rejection, on every raw argument list. -/
def ExactMacroCalibration : Prop :=
  ∀ (e : Nat.Partrec.Code) (p : Policy), RealizesPolicy e p →
    ∀ (tag n : Nat) (xs : List Nat),
      macroEval (e,tag,n,xs) = Part.some (PolicyShape.macroCode p tag n xs)

/-- First supplied-policy uniformity bridge. This is not the complete
source compiler or the uniform ground-comparison theorem. -/
def FullSuppliedCodeMacro : Prop := MacroPartrec ∧ ExactMacroCalibration

end LogicLineages.PermittedControl.PolicySuppliedCodeMacro
