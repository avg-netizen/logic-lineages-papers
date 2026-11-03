module
public import LogicLineages.OrdinalComparison.ActiveScalarAnnotationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AdditiveHeadTree
open ActiveScalarAnnotation

/-- Literal additive grade-one head tree: tracked F1, whole genuinely F-free
positive leaves, and binary addition. Opaque free leaves keep all their syntax. -/
inductive HeadTree {k Γ} (F : Variable Γ (Ty.curriedGround (k+1))) : OrdinalExpression Γ → Prop where
  | free {e} (grade : GeneratedOrdinalGrade Γ 1 e) (inactive : ¬ Active F e) : HeadTree F e
  | tracked : HeadTree F (.var ⟨_,F,UnaryCarrier.headIndex k⟩)
  | add {a b} (ha : HeadTree F a) (hb : HeadTree F b) : HeadTree F (.add a b)

/-- Simultaneous scalar invariant needed for nested ground lambdas. This is
separate from actual operator annotations: it records grade-zero scalar trees
whose active collapse heads have literal additive HeadTree certificates. -/
inductive ScalarTrees {k Γ} (F : Variable Γ (Ty.curriedGround (k+1))) : OrdinalExpression Γ → Prop where
  | free {e} (grade : GeneratedOrdinalGrade Γ 0 e) (inactive : ¬ Active F e) : ScalarTrees F e
  | tracked : ScalarTrees F (.var ⟨_,F,0⟩)
  | add {a b} (ha : ScalarTrees F a) (hb : ScalarTrees F b) : ScalarTrees F (.add a b)
  | collapse {h t} (head : HeadTree F h) (tail : ScalarTrees F t) : ScalarTrees F (.collapse h t)
end LogicLineages.OrdinalComparison.Source.AdditiveHeadTree
