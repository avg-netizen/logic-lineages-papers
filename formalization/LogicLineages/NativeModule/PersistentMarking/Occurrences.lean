module

public import LogicLineages.NativeModule.PersistentMarking.SpineSyntax

@[expose] public section

namespace LogicLineages.PersistentMarking.Spine

inductive At : Args → Nat → Expr → Prop where
  | here : At (.cons q qs) 0 q
  | there : At qs i q → At (.cons x qs) (i+1) q

/-- One occurrence, not all equal-valued occurrences, is removed. -/
inductive Remove : Args → Expr → Args → Prop where
  | here : Remove (.cons q qs) q qs
  | there : Remove qs q rest → Remove (.cons x qs) q (.cons x rest)

/-- Ordered subsequences retain multiplicity. Their interleaving is explicit. -/
inductive Split : Args → Args → Args → Prop where
  | nil : Split .nil .nil .nil
  | left : Split xs ys zs → Split (.cons x xs) (.cons x ys) zs
  | right : Split xs ys zs → Split (.cons x xs) ys (.cons x zs)

def Nonempty : Args → Prop
  | .nil => False
  | .cons _ _ => True

/-- All finite arrow prefixes, including the empty prefix with any residual
result type. No maximal-to-ground decomposition is imposed. -/
def ArrowPrefix : List Ty → Ty → Ty
  | [], τ => τ
  | σ::types, τ => .arrow σ (ArrowPrefix types τ)

/-- Self copies retain original head, base and extras, changing output only. -/
def ownerCopies (f : Head) (base extras : Args) : List Ty → Args
  | [] => .nil
  | σ::types => .cons (.marked f σ base extras) (ownerCopies f base extras types)

end LogicLineages.PersistentMarking.Spine
