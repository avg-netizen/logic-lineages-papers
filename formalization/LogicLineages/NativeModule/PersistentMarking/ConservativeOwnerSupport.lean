module

public import LogicLineages.NativeModule.PersistentMarking.ConservativeListSupport
public import LogicLineages.NativeModule.PersistentMarking.RefinementFullCallProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ConservativeOwnerSupport
open Spine AuxiliaryReflexivityProof

theorem prefixRefl (xs : Args) : Prefix xs xs := by
  cases xs with
  | nil => exact .nil
  | cons x xs => exact .cons (prefixRefl xs)
termination_by sizeOf xs

theorem wholeTuple (f : Head) (base extras : Args) (types : List Ty) :
    PrefixTuple f base extras types (ownerCopies f base extras types) := by
  induction types with
  | nil => exact .nil
  | cons σ types ih => exact .cons (.intro (prefixRefl extras)) ih

theorem wholeCopies (f : Head) (base extras : Args) (types : List Ty) :
    PrefixCopies f base extras (ownerCopies f base extras types) := by
  induction types with
  | nil => exact .nil
  | cons σ types ih => exact .cons (.intro (prefixRefl extras)) ih

theorem tupleTyped (S : Signature) (f : Head) (ρ : Ty) (base extras : Args)
    (hp : PaperTerm S (.marked f ρ base extras) ρ) {types : List Ty} {args : Args}
    (h : PrefixTuple f base extras types args) (τ : Ty) : CallTyped EmptyContext (ArrowPrefix types τ) args τ := by
  induction h with
  | nil => exact .nil
  | @cons σ q types qs hc hs ih =>
    cases hc with
    | @intro pref σ hprefix =>
      obtain ⟨h⟩ := OwnerRefinementProof.prefixOmission S f σ base extras pref (retypePaper S f ρ σ base extras hp) hprefix
      exact .cons (RefinementSubstitutionSupport.endpoints h).2.1 ih

theorem appendNil (xs : Args) : xs.append .nil = xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp only [Args.append,appendNil xs]
termination_by sizeOf xs

theorem ownerApplication (S : Signature) (f : Head) (τ : Ty) (base extras : Args)
    (hp : PaperTerm S (.marked f τ base extras) τ) (types : List Ty) :
    apply (.marked f (ArrowPrefix types τ) base extras) (ownerCopies f base extras types) =
      some (.marked f τ base (extras.append (ownerCopies f base extras types))) := by
  cases types with
  | nil => simp only [ArrowPrefix,ownerCopies,apply,appendNil]
  | cons σ types =>
    have ht := tupleTyped S f τ base extras hp (wholeTuple f base extras (σ::types)) τ
    have hc := SpineCallTypingProof.consumeExact _ _ _ _ ht
    simp only [ownerCopies,ArrowPrefix] at hc ⊢
    simp only [apply,applyAux,hc,Option.map_some,SubstitutionProof.emptyArgsSubstitution]

theorem ownerExpansion (S : Signature) (f : Head) (τ : Ty) (base extras : Args)
    (hp : PaperTerm S (.marked f τ base extras) τ) (types : List Ty) :
    Refines S (.marked f τ base extras) (.marked f τ base (extras.append (ownerCopies f base extras types))) :=
  OwnerRefinementProof.prefixExpansion S f τ base extras _ hp (wholeCopies f base extras types)
theorem prefixAppend (xs ys : Args) : Prefix xs (xs.append ys) := by
  cases xs with
  | nil => exact .nil
  | cons x xs => exact .cons (prefixAppend xs ys)
termination_by sizeOf xs

end LogicLineages.PersistentMarking.ConservativeOwnerSupport
