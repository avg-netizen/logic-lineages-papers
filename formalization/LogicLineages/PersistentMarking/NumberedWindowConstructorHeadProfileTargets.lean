import LogicLineages.PersistentMarking.NumberedWindowConstructorArgumentAddressTargets

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorHeadProfileTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary NumberedWindowArithmeticLeastClass
open NumberedWindowConstructorArgumentAddresses

def addressSetoid : Setoid (List (Option Nat)) where
  r := List.Perm
  iseqv := ⟨List.Perm.refl, List.Perm.symm, List.Perm.trans⟩

structure HeadProfile where
  result : Ty
  rank : Option Nat
  label : Option Nat
  base : Quotient addressSetoid
  extras : List (Option Nat)

def headProfile (S : Spine.Signature) (K Γ : List Ty) : NTerm → Option HeadProfile
  | .ordinary f bs =>
    some ⟨f.result, Spine.classRank S f, none, Quotient.mk addressSetoid (bs.toList.map (slot S K Γ)), []⟩
  | .numbered f τ k bs es =>
    some ⟨τ, Spine.classRank S f, some k, Quotient.mk addressSetoid (bs.toList.map (slot S K Γ)), es.toList.map (slot S K Γ)⟩
  | _ => none

def PrimaryHeadProfile : Prop :=
  ∀ S K Γ τ q r, DecisionSourceUniverse.Closed K → InWindow S K (finiteC Γ) τ q →
    Primary S K (finiteC Γ) τ q r → headProfile S K Γ q = headProfile S K Γ r

def AddressBagExact : Prop :=
  ∀ xs ys : List (Option Nat), (Quotient.mk addressSetoid xs = Quotient.mk addressSetoid ys) ↔ xs.Perm ys

def SameSlotComputable : Prop :=
  ∀ S K Γ (hk : DecisionSourceUniverse.Closed K) q r,
    InWindow S K (finiteC Γ) q.type q → InWindow S K (finiteC Γ) r.type r →
    slot S K Γ q = slot S K Γ r → (ComputableArgument S K Γ hk q ↔ ComputableArgument S K Γ hk r)

end LogicLineages.PersistentMarking.NumberedWindowConstructorHeadProfileTargets
