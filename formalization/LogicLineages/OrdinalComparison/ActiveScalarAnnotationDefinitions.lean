module
public import LogicLineages.OrdinalComparison.GroundOperatorDischargeDefinitions
public import LogicLineages.OrdinalComparison.SourceAssignmentSupportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActiveScalarAnnotation
open SourceFreeOccurrences

/-- Activity means the actual typed tracked name occurs, not a freely supplied
Boolean label or semantic oracle. -/
def Active {k Γ} (F : Variable Γ (Ty.curriedGround (k+1))) (e : OrdinalExpression Γ) : Prop :=
  (⟨Ty.curriedGround (k+1),F⟩ : PackedVariable Γ) ∈ AssignmentSupport.names e

/-- Actual-operator annotations for the tracked active scalar branch. A truly
F-free piece is a whole stop; its opaque internals need no annotation. A collapse
requires an explicit original source operator for its exact head, and actual
head-name activity must imply tail-name activity. This is not a definition of
which source terms are allowed: the actual-source target proves construction. -/
inductive Annotated {k Γ} (p : AdmissibleSum.Policy)
    (F : Variable Γ (Ty.curriedGround (k+1))) : OrdinalExpression Γ → Prop where
  | free {e} (h : ¬ Active F e) : Annotated p F e
  | tracked : Annotated p F (.var ⟨_,F,0⟩)
  | add {a b} (ha : Annotated p F a) (hb : Annotated p F b) : Annotated p F (.add a b)
  | collapse {h t} (operator : GroundOperatorDischarge.OperatorWitness p h)
      (support : Active F h → Active F t) (tail : Annotated p F t) : Annotated p F (.collapse h t)
end LogicLineages.OrdinalComparison.Source.ActiveScalarAnnotation
