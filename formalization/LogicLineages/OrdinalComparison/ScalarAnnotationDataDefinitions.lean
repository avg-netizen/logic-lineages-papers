module
public import LogicLineages.OrdinalComparison.AdditiveHeadTreeDefinitions
public import LogicLineages.OrdinalComparison.ActiveScalarAnnotationDefinitions
public import LogicLineages.OrdinalComparison.WWDefaultPolicyDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScalarAnnotationData
open ActiveScalarAnnotation AdditiveHeadTree

/-- Raw computational operator data: no Prop existence witness is eliminated
and no arbitrary head is asserted to have an original source. Valid checks the
stored WHOLE vector against the stored actual source. -/
structure Operator (Γ : List Ty) where
  arity : Nat
  source : OriginalTerm Γ (Ty.curriedGround (arity+1))
  vector : OrdinalVector Γ (Ty.curriedGround (arity+1)).level

def Operator.head {Γ} (op : Operator Γ) : OrdinalExpression Γ := op.vector (UnaryCarrier.headIndex op.arity)

def closeOperator {Γ} (op : Operator (.ground :: Γ)) : Operator Γ :=
  ⟨op.arity,GroundOperatorDischarge.close op.source,fun j => ordinalHeadClosure (op.vector j)⟩

inductive Tree (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1))) : Type where
  | free (q : OrdinalExpression Γ)
  | tracked
  | add (a b : Tree k Γ F)
  | collapse (op : Operator Γ) (tail : Tree k Γ F)

def erase {k Γ F} : Tree k Γ F → OrdinalExpression Γ
  | .free q => q
  | .tracked => .var ⟨_,F,0⟩
  | .add a b => .add (erase a) (erase b)
  | .collapse op tail => .collapse op.head (erase tail)

/-- Semantic correctness predicate for raw data. It is not a source-grammar
restriction and is not a premise in the later actual-source builder. -/
def Valid {k Γ F} : Tree k Γ F → Prop
  | .free q => GeneratedOrdinalGrade Γ 0 q ∧ ¬ Active F q
  | .tracked => True
  | .add a b => Valid a ∧ Valid b
  | .collapse op tail =>
      AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy op.source = some op.vector ∧
      HeadTree F op.head ∧ (Active F op.head → Active F (erase tail)) ∧ Valid tail

def closeTree {k Γ} {F : Variable Γ (Ty.curriedGround (k+1))} :
    Tree k (.ground :: Γ) (.there F) → Tree k Γ F
  | .free q => .free (ordinalHeadClosure q)
  | .tracked => .tracked
  | .add a b => .add (closeTree a) (closeTree b)
  | .collapse op tail => .collapse (closeOperator op) (closeTree tail)

/-- Deterministic whole-free-first ground scalar partial on operator data.
Invalid data may fail or have no semantic meaning; Valid inputs must be proved
successful and exact. Every stored operator is transformed by literal closing. -/
def groundPartial {k Γ} {F : Variable Γ (Ty.curriedGround (k+1))}
    (d : Tree k (.ground :: Γ) (.there F)) : Option (Tree k Γ F) :=
  if ordinalHeadFree (erase d) then some (.add (closeTree d) (.free .one)) else
  match d with
  | .free q => (AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 q).map (fun v => .free (v 0))
  | .tracked => none
  | .add a b => do
      let a' ← groundPartial a
      let b' ← groundPartial b
      pure (.add (.add a' b') (.free .one))
  | .collapse op tail => do
      let tail' ← groundPartial tail
      pure (.collapse (closeOperator op) tail')
end LogicLineages.OrdinalComparison.Source.ScalarAnnotationData
