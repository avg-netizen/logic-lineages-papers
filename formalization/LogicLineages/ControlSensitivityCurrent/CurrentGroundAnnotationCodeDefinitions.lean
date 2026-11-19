module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationDefinitions
public import LogicLineages.StandardControlCurrent.PolicyAssignmentDefinitions
public import LogicLineages.OrdinalComparison.CanonicalAnnotationBuilderCodeDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationCode

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open AdmissibleSum SourceAnnotationCode TrackedSourceInspectionCode

/-- Annotation joins differ from ordinary ordinal joins: the literal tag here
is scalar-annotation tag 2, and operator payloads remain opaque. -/
def markStep : PolicyShape.State → Bool → PolicyShape.State
  | none, _ => none
  | some ([], _), false => none
  | some (x::xs, stack), false => some (xs,x::stack)
  | some (xs, r::l::stack), true => some (xs,(4*Nat.pair l r+2)::stack)
  | some (_, _), true => none

def run (script : List Bool) (state : PolicyShape.State) : PolicyShape.State :=
  script.foldl markStep state

def macroCode (p : Policy) (site n : Nat) (xs : List Nat) : Option Nat :=
  PolicyShape.finish (run (PolicyShape.selector p site n) (some (xs,[])))

def repeatCode (p : Policy) (count t : Nat) : Option Nat :=
  if count=0 then some 0 else
    macroCode p (PolicyShape.siteCode .scalarRepeat) (count-1) (List.replicate count t)

/-- Literal ground partial on the annotation code before deleting ground slot
zero. Only the selected policy macro is expanded. -/
def groundPartialCode (p : Policy) (trackedIndex : Nat) : Nat → Option Nat
  | n =>
    if OrdinalSyntax.headFree (eraseCode trackedIndex n) then
      some (4*Nat.pair (closeCode n) 4+2)
    else if h0 : n%4=0 then
      (PolicyPartial.run p 0 0 (n/4)).map (fun v => 4*v.getD 0 0)
    else if h1 : n%4=1 then none
    else
      have hd : n/4<n := Nat.div_lt_self (by omega) (by decide)
      let q := (n/4).unpair
      have hl : q.1<n := (Nat.unpair_left_le _).trans_lt hd
      have hr : q.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%4=2 then do
        let a ← groundPartialCode p trackedIndex q.1
        let b ← groundPartialCode p trackedIndex q.2
        macroCode p (PolicyShape.siteCode .activeAdd) 2 [a,b,4]
      else (groundPartialCode p trackedIndex q.2).map (fun tail =>
        4*Nat.pair (closeOperatorCode q.1) tail+3)
termination_by n => n
decreasing_by all_goals assumption

def lambdaData (p : Policy) (tracked : Nat) (body : List Nat × Nat) : Option Nat := do
  let pd ← groundPartialCode p (tracked+1) body.2
  let d ← repeatCode p (2*((body.1.map OrdinalSyntax.partialSize).sum)) pd
  pure (4*Nat.pair d (closeCode body.2)+2)

/-- No old-policy builder is called. The literal source's F-free test has
precedence over any structural recursion into its opaque internals. -/
def buildCode (p : Policy) (Γ : List Nat) (tracked : Nat) : Nat → Option (List Nat × Nat)
  | n => do
    let τ ← SyntaxCode.check Γ n
    let arity ← arityCode τ
    let u ← PolicyAssignment.assignmentCode p Γ n
    if occursCode tracked n = false then pure (u,4*u.getD 0 0)
    else if n%8=0 then if n/8=tracked then pure (u,1) else none
    else if h : n%8=5 ∨ n%8=6 then
      have hd : n/8<n := Nat.div_lt_self (by omega) (by decide)
      let q := (n/8).unpair
      have hl : q.1<n := (Nat.unpair_left_le _).trans_lt hd
      have hr : q.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%8=5 then do
        let argType ← SyntaxCode.check Γ q.2
        if argType=0 then
          let a ← buildCode p Γ tracked q.1
          let b ← buildCode p Γ tracked q.2
          pure (u,CanonicalAnnotationBuilderCode.appData arity q.1 a b)
        else none
      else if q.1=0 then do
        let b ← buildCode p (0::Γ) (tracked+1) q.2
        let d ← lambdaData p tracked b
        pure (u,d)
      else none
    else none
termination_by n => n
decreasing_by all_goals assumption

end LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationCode
