module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalIDOperatorTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalIDTagProof
open Spine NumberedWindowArithmeticAllContextTargets NumberedWindowArithmeticDirectCodeTargets
open NumberedWindowExternalIDOperators NumberedWindowExternalIDOperatorTargets

theorem scalarInjective : Function.Injective tagScalar := by
  intro a b h
  unfold tagScalar at h
  omega

theorem multisetInjective : Function.Injective tagMultiset := by
  intro a b h
  unfold tagMultiset at h
  omega

theorem disjoint (a b : Nat) : tagScalar a ≠ tagMultiset b := by
  intro h
  unfold tagScalar tagMultiset at h
  omega

theorem tags : ExactDisjointOperatorTags :=
  ⟨scalarInjective,multisetInjective,disjoint⟩

theorem scalarAt (S : Signature) (K : List Ty) (P : Pred) (n : Nat) :
    taggedStep S K P (tagScalar n) ↔ scalarStep S K (fun x => P (tagScalar x)) n := by
  constructor
  · intro h
    rcases h with ⟨x,e,hx⟩ | ⟨x,e,_⟩
    · have he : n = x := scalarInjective e
      subst x
      exact hx
    · exact False.elim (disjoint n x e)
  · intro h
    exact Or.inl ⟨n,rfl,h⟩

theorem multisetAt (S : Signature) (K : List Ty) (P : Pred) (n : Nat) :
    taggedStep S K P (tagMultiset n) ↔ multisetStep S K (fun x => P (tagMultiset x)) n := by
  constructor
  · intro h
    rcases h with ⟨x,e,_⟩ | ⟨x,e,hx⟩
    · exact False.elim (disjoint x n e.symm)
    · have he : n = x := multisetInjective e
      subst x
      exact hx
  · intro h
    exact Or.inr ⟨n,rfl,h⟩

theorem projection : ExactTaggedClauseProjection :=
  fun S K P n => ⟨scalarAt S K P n,multisetAt S K P n⟩

theorem guardedMono (G : Pred) (R : Nat → Nat → Prop) : IsMonotone (guardedStep G R) := by
  intro P Q h n hn
  exact ⟨hn.1,fun m hm => h m (hn.2 m hm)⟩

theorem scalarMono (S : Signature) (K : List Ty) : IsMonotone (scalarStep S K) :=
  guardedMono (AdmittedAddress S K) (AddressPositive S K)

theorem multisetMono (S : Signature) (K : List Ty) : IsMonotone (multisetStep S K) :=
  guardedMono (AdmittedAddressListCode S K) (DirectAtCode S K)

theorem taggedMono (S : Signature) (K : List Ty) : IsMonotone (taggedStep S K) := by
  intro P Q h n hn
  rcases hn with ⟨x,e,hx⟩ | ⟨x,e,hx⟩
  · exact Or.inl ⟨x,e,scalarMono S K _ _ (fun y => h (tagScalar y)) x hx⟩
  · exact Or.inr ⟨x,e,multisetMono S K _ _ (fun y => h (tagMultiset y)) x hx⟩

theorem monotone : ActualOperatorsMonotone :=
  fun S K => ⟨scalarMono S K,multisetMono S K,taggedMono S K⟩

end LogicLineages.PersistentMarking.NumberedWindowExternalIDTagProof
