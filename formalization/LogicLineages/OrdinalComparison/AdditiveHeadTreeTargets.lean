module
public import LogicLineages.OrdinalComparison.AdditiveHeadTreeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AdditiveHeadTree.Targets

def HeadClosureHead : Prop := ∀ (k : Nat) (Γ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (h : OrdinalExpression (.ground :: Γ)),
  HeadTree (.there F) h → HeadTree F (ordinalHeadClosure h)

def HeadClosureScalar : Prop := ∀ (k : Nat) (Γ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (q : OrdinalExpression (.ground :: Γ)),
  ScalarTrees (.there F) q → ScalarTrees F (ordinalHeadClosure q)

/-- Grade distinctions are derived from the input certificate. Only actual
successful scalar runs are claimed, not totality of arbitrary expressions. -/
def GroundPartialTrees : Prop := ∀ (k : Nat) (Γ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (p : AdmissibleSum.Policy)
    (q : OrdinalExpression (.ground :: Γ)) (v : OrdinalPartialVector Γ .ground),
  ScalarTrees (.there F) q → AdmissiblePartial.run p 0 q = some v →
    ScalarTrees F (v 0) ∧ HeadTree F (v 1)

/-- Both invariants are genuinely built from every actual original tracked
source, all result arities and every structural policy. The whole assignment
exists without any supplied head-tree, scalar, annotation, or grade premise. -/
def ActualSourceTrees : Prop := ∀ (k : Nat) (Γ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (n : Nat)
    (p : AdmissibleSum.Policy) (e : TrackedSource.Expr k Γ F n),
  ∃ u : OrdinalVector Γ (Ty.curriedGround n).level,
    AdmissibleAssignment.assignment p (TrackedSource.erase e) = some u ∧
    ScalarTrees F (u 0) ∧ ∀ j, 0 < j.val → HeadTree F (u j)
end LogicLineages.OrdinalComparison.Source.AdditiveHeadTree.Targets
