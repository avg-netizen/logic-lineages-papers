module
public import LogicLineages.OrdinalComparison.SourceAnnotationPartialCodeDefinitions
public import LogicLineages.OrdinalComparison.TrackedSourceInspectionCodeDefinitions
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.CanonicalAnnotationBuilderCode
open SourceAnnotationCode TrackedSourceInspectionCode

/-- Raw stored full operator payload and literal application annotation. -/
def appData (arity fn : Nat) (f a : List Nat × Nat) : Nat :=
  4*Nat.pair (Nat.pair arity (Nat.pair fn (Encodable.encode f.1)))
    (4*Nat.pair f.2 a.2+2)+3

/-- Ground lambda uses the complete actual child vector for its copy factor. -/
def lambdaData (tracked : Nat) (body : List Nat × Nat) : Option Nat := do
  let pd ← SourceAnnotationPartialCode.groundPartialCode (tracked+1) body.2
  let factor := 2*((body.1.map OrdinalSyntax.partialSize).sum)
  pure (4*Nat.pair (repeatCode factor pd) (closeCode body.2)+2)

/-- Canonical raw-source traversal. F-free blocks stop immediately, whatever
opaque internal types they contain. This does not choose an Expr witness or
claim annotation-data identity between distinct witnesses of one source. -/
def buildCode (Γ : List Nat) (tracked : Nat) : Nat → Option (List Nat × Nat)
  | n => do
    let τ ← SyntaxCode.check Γ n
    let arity ← arityCode τ
    let u ← DefaultSourceAssignment.assignmentCode Γ n
    if occursCode tracked n = false then pure (u,4*u.getD 0 0)
    else if n%8=0 then if n/8=tracked then pure (u,1) else none
    else if h : n%8=5 ∨ n%8=6 then
      have hd : n/8<n := Nat.div_lt_self (by omega) (by decide)
      let p := (n/8).unpair
      have hl : p.1<n := (Nat.unpair_left_le _).trans_lt hd
      have hr : p.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%8=5 then do
        let argType ← SyntaxCode.check Γ p.2
        if argType=0 then
          let f ← buildCode Γ tracked p.1
          let a ← buildCode Γ tracked p.2
          pure (u,appData arity p.1 f a)
        else none
      else if p.1=0 then do
        let body ← buildCode (0::Γ) (tracked+1) p.2
        let data ← lambdaData tracked body
        pure (u,data)
      else none
    else none
termination_by n => n
decreasing_by all_goals assumption
end LogicLineages.OrdinalComparison.Source.CanonicalAnnotationBuilderCode
