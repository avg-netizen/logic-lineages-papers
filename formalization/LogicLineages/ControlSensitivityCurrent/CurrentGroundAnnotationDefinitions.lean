module
public import LogicLineages.ControlSensitivityCurrent.CurrentReserveDefinitions
public import LogicLineages.OrdinalComparison.SourceAnnotationCodeDefinitions
public import LogicLineages.OrdinalComparison.UnitHeadCodeDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotation

open LogicLineages.OrdinalComparison.Source
open AdmissibleSum AdditiveHeadTree ActiveScalarAnnotation ScalarAnnotationData

/-- Validity is for the chosen policy, the stored actual source and its
complete vector. It is an output of build, not a generated-source premise. -/
def Valid (p : Policy) {k Γ F} : Tree k Γ F → Prop
  | .free q => GeneratedOrdinalGrade Γ 0 q ∧ ¬ Active F q
  | .tracked => True
  | .add a b => Valid p a ∧ Valid p b
  | .collapse op tail =>
      AdmissibleAssignment.assignment p op.source = some op.vector ∧
      HeadTree F op.head ∧ (Active F op.head → Active F (erase tail)) ∧ Valid p tail

def expandTree {k Γ F n} : Shape n → (Fin n → Tree k Γ F) → Tree k Γ F
  | .leaf, xs => xs 0
  | .join a b, xs =>
    .add (expandTree a (fun i => xs (Fin.castAdd _ i)))
      (expandTree b (fun i => xs (Fin.natAdd _ i)))

def repeatTree (p : Policy) {k Γ F} (d : Tree k Γ F) : Nat → Tree k Γ F
  | 0 => .free .zero
  | n+1 => expandTree (p.shape .scalarRepeat n) (fun _ => d)

def threeTree (p : Policy) {k Γ F} (a b : Tree k Γ F) : Tree k Γ F :=
  expandTree (p.shape .activeAdd 2) (Fin.cases a
    (Fin.cases b (fun _ => .free .one)))

/-- Actual priority-sensitive ground partial on the annotation. Copying keeps
the exact selected shape and applies literal ground closing to every operator. -/
def groundPartial (p : Policy) {k Γ} {F : Variable Γ (Ty.curriedGround (k+1))}
    (d : Tree k (.ground :: Γ) (.there F)) : Option (Tree k Γ F) :=
  if ordinalHeadFree (erase d) then some (.add (closeTree d) (.free .one)) else
  match d with
  | .free q => (AdmissiblePartial.run p 0 q).map (fun v => .free (v 0))
  | .tracked => none
  | .add a b => do
      let ar ← groundPartial p a
      let br ← groundPartial p b
      pure (threeTree p ar br)
  | .collapse op tail => do
      let tr ← groundPartial p tail
      pure (.collapse (closeOperator op) tr)

/-- Canonical traversal on the typed original tree. A whole F-free subtree
stops even if its witness uses an active grammar constructor. Its actual
whole vector is retained, not synthesized from the scalar. -/
def build (p : Policy) {k Γ F n} (e : TrackedSource.Expr k Γ F n) :
    Option (OrdinalVector Γ (Ty.curriedGround n).level × Tree k Γ F) :=
  match e with
  | .tracked => some ((fun j => .var ⟨_,F,j⟩),.tracked)
  | .ground x => some ((fun j => .var ⟨_,x,j⟩),.free (.var ⟨_,x,0⟩))
  | .free t _ => do
      let u ← AdmissibleAssignment.assignment p t
      pure (u,.free (u 0))
  | @TrackedSource.Expr.app _ _ _ r a b => do
      let u ← AdmissibleAssignment.assignment p (TrackedSource.erase (.app a b))
      if TrackedSource.active (TrackedSource.Expr.app a b) then
        let (ua,da) ← build p a
        let (_,db) ← build p b
        pure (u,.collapse ⟨r,TrackedSource.erase a,ua⟩ (.add da db))
      else pure (u,.free (u 0))
  | .lam body => do
      let u ← AdmissibleAssignment.assignment p (TrackedSource.erase (.lam body))
      if TrackedSource.active (TrackedSource.Expr.lam body) then
        let (ub,db) ← build p body
        let pd ← groundPartial p db
        let factor := 2*((List.ofFn ub).map ordinalPartialSize).sum
        pure (u,.add (repeatTree p pd factor) (closeTree db))
      else pure (u,.free (u 0))

end LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotation
