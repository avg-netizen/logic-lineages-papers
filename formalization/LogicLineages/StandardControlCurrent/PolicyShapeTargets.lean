module
public import LogicLineages.StandardControlCurrent.PolicyShapeDefinitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyShapeTargets
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax PolicyShape

def Sites : Prop := ∀ s : MacroSite, decodeSite (siteCode s)=s

def FramedExpansion : Prop := ∀ (Γ : List Ty) (n : Nat) (s : Shape n)
    (xs : Fin n → OrdinalExpression Γ) (rest stack : List Nat),
  run (shapeCode s) (some (List.ofFn (fun i => typedCode (xs i)) ++ rest, stack)) =
    some (rest, typedCode (expand s xs)::stack)

def RawPrograms : Prop :=
  Primrec (fun x : State × Bool => step x.1 x.2) ∧
  Primrec (fun x : List Bool × State => run x.1 x.2) ∧
  Primrec finish ∧ Primrec (fun x : List Bool × List Nat => expandCode x.1 x.2)

def PolicyPrograms : Prop := ∀ p : Policy, Effective p →
  Computable (fun x : Nat × Nat × List Nat => macroCode p x.1 x.2.1 x.2.2) ∧
  Computable (fun x : Nat × Nat × Nat => PolicyShape.repeatCode p x.1 x.2.1 x.2.2)

def LiteralCalibration : Prop :=
  (∀ (p : Policy) (site : MacroSite) (Γ : List Ty) (n : Nat)
      (xs : Fin (n+1) → OrdinalExpression Γ),
    macroCode p (siteCode site) n (List.ofFn (fun i => typedCode (xs i))) =
      some (typedCode (expand (p.shape site n) xs))) ∧
  (∀ (p : Policy) (site : MacroSite) (Γ : List Ty) (count : Nat) (t : OrdinalExpression Γ),
    PolicyShape.repeatCode p (siteCode site) count (typedCode t) =
      some (typedCode (AdmissibleAssignment.repeated p site count t)))

/-- Supporting actual macro program bridge, not complete source assignment. -/
def FullPolicyShape : Prop := Sites ∧ FramedExpansion ∧ RawPrograms ∧ PolicyPrograms ∧ LiteralCalibration
end LogicLineages.StandardControlCurrent.PolicyShapeTargets
