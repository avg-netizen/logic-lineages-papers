module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerTransition
open FirstOrder Language CotreePresburger

section
variable {Q A : Type} [Fintype Q] [LinearOrder Q] [Fintype A] [LinearOrder A]

/-- Source equation (5): select exactly the subset of attainable root states. -/
def subsetFormula (δ : Q → Q → Q) (S : Finset Q) : PFormula (Finset Q) :=
  allOf (fun q : Q => (truth (q ∈ S)).iff (formula δ q))

/-- Sum counts of child types with the given state-subset label. -/
def projectionTerm (label : A → Finset Q) (B : Finset Q) : PTerm A :=
  sumAll (fun a : A => if label a = B then .var a else 0)

def projectedCounts (label : A → Finset Q) (counts : A → Nat) (B : Finset Q) : Nat :=
  ∑ a, if label a = B then counts a else 0

def totalTerm : PTerm A := sumAll (fun a : A => .var a)

/-- The source's linear child-count substitution, arity at least two, and
zero counts outside the permitted child-root kinds. `label` and `allowed` are
finite input tables, not assumptions supplying a missing theorem. -/
def horizontalFormula (δ : Q → Q → Q) (S : Finset Q)
    (label : A → Finset Q) (allowed : A → Bool) : PFormula A :=
  (subsetFormula δ S).subst (projectionTerm label) ⊓
    (positive (totalTerm (A := A)) ⊓ ((totalTerm (A := A)).equal 1).not) ⊓
    allOf (fun a : A => (truth (allowed a = false)).imp ((.var a : PTerm A).equal 0))
end
end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerTransition
