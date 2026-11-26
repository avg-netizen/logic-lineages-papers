import LogicLineages.PersistentMarking.NumberedWindowDomain
import LogicLineages.PersistentMarking.Occurrences

namespace LogicLineages.PersistentMarking.NumberedWindowRules
open Spine NumberedWindowSyntax NumberedWindowDomain

/-- A primitive replacement may lower an already numbered head strictly;
it is not the identical persistent symbolic mark. Only the common initial
lambda spine is traversed. The arguments, label-free head and types remain
literally unchanged. -/
inductive MarkDecrease : NTerm → NTerm → Prop where
  | omega : MarkDecrease (.ordinary f bs) (.numbered f f.result k bs .nil)
  | finite : l < k → MarkDecrease (.numbered f τ k bs es) (.numbered f τ l bs es)
  | lam : MarkDecrease body result → MarkDecrease (.lam σ body) (.lam σ result)

def PrimitiveReplacement (source target : NArgs) : Prop :=
  ∃ kept removed added : List NTerm,
    source.toList.Perm (kept ++ removed) ∧ target.toList.Perm (kept ++ added) ∧
      removed ≠ [] ∧ ∀ a ∈ added, ∃ b ∈ removed, MarkDecrease b a

/-- Source rule shapes. WindowStep below imposes original typedness and
declaration-retaining window admission of both endpoints. In particular
this has function-side auxiliary application closure only. -/
mutual
inductive RawStep (S : Signature) (K : List Ty) : NTerm → NTerm → Prop where
  | mark : RawStep S K (.ordinary f bs) (.numbered f f.result k bs .nil)
  | lower : RawStep S K (.numbered f τ (k + 1) bs es) (.numbered f τ k bs es)
  | select :
      (bs.get i = some selected ∨ es.get i = some selected) →
      selected.type = ArrowPrefix domains τ →
      applications selected (ownerCopies f k bs es domains) = some result →
      RawStep S K (.numbered f τ (k + 1) bs es) result
  | copy :
      Precedes S f g → HeadInWindow S K g →
      RawStep S K (.numbered f g.result (k + 1) bs es)
        (.ordinary g (ownerCopies f k bs es g.arguments))
  | stat :
      Equivalent S f g → HeadInWindow S K g → PrimitiveReplacement bs target →
      RawStep S K (.numbered f g.result (k + 1) bs es) (.ordinary g target)
  | fabs :
      RawStep S K (.numbered f (.arrow σ τ) (k + 1) bs es)
        (.lam σ (openNumbered f σ τ k bs es))
  | beta :
      RawStep S K (.auxApp σ τ (.lam σ body) a) (substitute (.cons a .nil) 0 body)
  | bottom : q ≠ .bottom q.type → RawStep S K q (.bottom q.type)
  | lam : RawStep S K q r → RawStep S K (.lam σ q) (.lam σ r)
  | ordinaryBase : RawArgsStep S K bs target → RawStep S K (.ordinary f bs) (.ordinary f target)
  | numberedBase :
      RawArgsStep S K bs target → RawStep S K (.numbered f τ k bs es) (.numbered f τ k target es)
  | numberedExtra :
      RawArgsStep S K es target → RawStep S K (.numbered f τ k bs es) (.numbered f τ k bs target)
  | auxFunction :
      RawStep S K q r → RawStep S K (.auxApp σ τ q a) (.auxApp σ τ r a)
inductive RawArgsStep (S : Signature) (K : List Ty) : NArgs → NArgs → Prop where
  | first : RawStep S K q r → RawArgsStep S K (.cons q tail) (.cons r tail)
  | later : RawArgsStep S K tail target → RawArgsStep S K (.cons q tail) (.cons q target)
end

def WindowStep (S : Signature) (K : List Ty) (C : BoundContext) (τ : Ty)
    (q r : NTerm) : Prop :=
  RawStep S K q r ∧ InWindow S K C τ q ∧ InWindow S K C τ r

/-- Raw finite paths in one unchanged universe, allowing the empty path.
Every visited term, including the endpoints of a zero-step path, carries
the very same signature, finite window, binding context and result type. -/
inductive WindowPath (S : Signature) (K : List Ty) (C : BoundContext) (τ : Ty) :
    NTerm → NTerm → Prop where
  | refl : InWindow S K C τ q → WindowPath S K C τ q q
  | next : WindowStep S K C τ q r → WindowPath S K C τ r t → WindowPath S K C τ q t

end LogicLineages.PersistentMarking.NumberedWindowRules
