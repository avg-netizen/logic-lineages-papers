module
public import LogicLineages.OrdinalComparison.ActiveScalarAnnotationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActiveScalarAnnotation.Targets

/-- Ground unit substitution preserves actual operator witnesses, as literal
source zero discharge, and the head-to-tail activity implication. -/
def HeadClosureTransport : Prop := ∀ (k : Nat) (Γ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (p : AdmissibleSum.Policy)
    (q : OrdinalExpression (.ground :: Γ)),
  Annotated p (.there F) q → Annotated p F (ordinalHeadClosure q)

/-- Generic scalar partial transport is conditional on an actual successful
run. It asserts no totality for arbitrary input expressions. -/
def GroundPartialTransport : Prop := ∀ (k : Nat) (Γ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (p : AdmissibleSum.Policy)
    (q : OrdinalExpression (.ground :: Γ)) (v : OrdinalPartialVector Γ .ground),
  Annotated p (.there F) q → AdmissiblePartial.run p 0 q = some v → Annotated p F (v 0)

/-- Annotation existence is derived for the complete original tracked grammar,
including captured opaque blocks and nested functional-result ground lambdas.
No annotation, operator or head-to-tail support premise is assumed. -/
def ActualSourceAnnotation : Prop := ∀ (k : Nat) (Γ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (n : Nat)
    (p : AdmissibleSum.Policy) (e : TrackedSource.Expr k Γ F n),
  ∃ u : OrdinalVector Γ (Ty.curriedGround n).level,
    AdmissibleAssignment.assignment p (TrackedSource.erase e) = some u ∧ Annotated p F (u 0)
end LogicLineages.OrdinalComparison.Source.ActiveScalarAnnotation.Targets
