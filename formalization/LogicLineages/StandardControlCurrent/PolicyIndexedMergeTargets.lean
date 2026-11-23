module
public import LogicLineages.StandardControlCurrent.PolicyIndexedShapeTargets
public import LogicLineages.StandardControlCurrent.PolicyPartialDefinitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedMerge
open OrdinalComparison.Source.AdmissibleSum (Policy)
open Nat.Partrec (Code)

abbrev CoordinateArgs := Code × Nat × Nat × Nat
abbrev MergeArgs := Code × Nat × Nat × List Nat × List Nat

noncomputable def firstOperand (x : CoordinateArgs) : Part (Option Nat) :=
  if x.2.1 = 5 then
    PolicyIndexedShape.macroCode (x.1,PolicyShape.siteCode .positiveRepeat,1,[x.2.2.1,x.2.2.1])
  else Part.some (some x.2.2.1)

noncomputable def coordinate (x : CoordinateArgs) : Part (Option Nat) :=
  (firstOperand x).bind fun
    | none => Part.some none
    | some a => PolicyIndexedShape.macroCode
        (x.1,PolicyShape.siteCode (if x.2.1 = 5 then .activeExp else .activeAdd),2,[a,x.2.2.2,1])

noncomputable def appendCoordinate (x : MergeArgs) (j : Nat)
    (acc : Option (List Nat)) : Part (Option (List Nat)) :=
  match acc with
  | none => Part.some none
  | some xs =>
    (coordinate (x.1,x.2.2.1,x.2.2.2.1.getD j 0,x.2.2.2.2.getD j 0)).map
      (Option.map (fun a => xs ++ [a]))

/-- Enumerate exactly the initial segment of coordinates in increasing order.
A returned refusal short-circuits subsequent policy calls. -/
noncomputable def prefixCode (x : MergeArgs) (k : Nat) : Part (Option (List Nat)) :=
  k.rec (Part.some (some [])) fun j ih => ih.bind (appendCoordinate x j)

noncomputable def merge (x : MergeArgs) : Part (Option (List Nat)) :=
  prefixCode x (x.2.1 + 2)

def ExactCoordinate : Prop :=
  ∀ (c : Code) (p : Policy), PolicyIndexedShape.Implements c p →
    ∀ tag a b, coordinate (c,tag,a,b) = Part.some (PolicyPartial.mergeCoordinate p tag a b)

def ExactMerge : Prop :=
  ∀ (c : Code) (p : Policy), PolicyIndexedShape.Implements c p →
    ∀ level tag a b, merge (c,level,tag,a,b) = Part.some (PolicyPartial.mergeCode p level tag a b)

end LogicLineages.StandardControlCurrent.PolicyIndexedMerge
