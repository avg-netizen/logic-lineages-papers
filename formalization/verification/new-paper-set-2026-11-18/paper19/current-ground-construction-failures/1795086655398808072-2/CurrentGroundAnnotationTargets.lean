module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationCodeDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationTargets

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open AdmissibleSum AdditiveHeadTree ActiveScalarAnnotation ScalarAnnotationData
open CurrentGroundAnnotation

/-- The marker interpreter has the ordered shape of the actual typed
expansion, with arbitrary residual streams and stacks. -/
def MarkerExpansion : Prop :=
  (∀ (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1))) (n : Nat)
      (s : Shape n) (xs : Fin n → Tree k Γ F) (rest stack : List Nat),
    CurrentGroundAnnotationCode.run (PolicyShape.shapeCode s)
      (some (List.ofFn (fun j => SourceAnnotationCode.code (xs j)) ++ rest,stack)) =
      some (rest,SourceAnnotationCode.code (expandTree s xs)::stack)) ∧
  (∀ (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1)))
      (p : Policy) (count : Nat) (d : Tree k Γ F),
    CurrentGroundAnnotationCode.repeatCode p count (SourceAnnotationCode.code d) =
      some (SourceAnnotationCode.code (CurrentGroundAnnotation.repeatTree p d count)))

def ValidTree : Prop :=
  ∀ (p : Policy) (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1)))
    (d : Tree k Γ F), Valid p d →
    ScalarTrees F (erase d) ∧ Annotated p F (erase d)

/-- Ground partial preserves actual operator annotations and its scalar
is the actual chosen-policy partial, not a reassociated value. -/
def ActualGroundPartial : Prop :=
  ∀ (p : Policy) (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1)))
    (d : Tree k (.ground :: Γ) (.there F)), Valid p d →
    ∃ (v : OrdinalPartialVector Γ .ground) (e : Tree k Γ F),
      AdmissiblePartial.run p 0 (erase d) = some v ∧
      CurrentGroundAnnotation.groundPartial p d = some e ∧
      erase e = v 0 ∧ Valid p e ∧
      (Active F (erase e) ↔ Active (.there F) (erase d)) ∧
      CurrentGroundAnnotationCode.groundPartialCode p (SourceTypedPorts.variableIndex (.there F))
        (SourceAnnotationCode.code d) = some (SourceAnnotationCode.code e)

/-- Neither assignment success nor annotation validity is a premise.
This theorem bridges the raw original code and the same typed canonical
annotation at any depth and for opaque original-syntax F-free blocks. -/
def ActualAnnotation : Prop :=
  ∀ (p : Policy) (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1))) (n : Nat)
    (e : TrackedSource.Expr k Γ F n),
    ∃ (u : OrdinalVector Γ (Ty.curriedGround n).level) (d : Tree k Γ F),
      CurrentGroundAnnotation.build p e = some (u,d) ∧
      AdmissibleAssignment.assignment p (TrackedSource.erase e) = some u ∧
      Valid p d ∧ erase d = u 0 ∧
      CurrentGroundAnnotationCode.buildCode p (Γ.map SyntaxCode.typeCode)
        (SourceTypedPorts.variableIndex F) (SyntaxCode.encodeTerm (TrackedSource.erase e)) =
          some (OrdinalSyntax.vectorCode u,SourceAnnotationCode.code d)

def AlgorithmsEffective : Prop :=
  ∀ p : Policy, PolicyShape.Effective p →
    Computable (fun z : Nat × Nat × List Nat => CurrentGroundAnnotationCode.macroCode p z.1 z.2.1 z.2.2) ∧
    Computable (fun z : Nat × Nat => CurrentGroundAnnotationCode.groundPartialCode p z.1 z.2) ∧
    Computable (fun z : List Nat × Nat × Nat => CurrentGroundAnnotationCode.buildCode p z.1 z.2.1 z.2.2)

def Full : Prop :=
  MarkerExpansion ∧ ValidTree ∧ ActualGroundPartial ∧ ActualAnnotation ∧ AlgorithmsEffective

end LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationTargets
