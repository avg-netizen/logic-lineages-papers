module

public import LogicLineages.NativeModule.PersistentMarking.StructuralStabilityTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.StructuralCoverageTargets
open Spine NameBridge StructuralContext

mutual
 def NamedOrdinary : Term → Prop
   | .var _ _ => True
   | .lam _ _ body => NamedOrdinary body
   | .head _ base => NamedOrdinaryArgs base
   | .marked _ _ _ _ => False
 def NamedOrdinaryArgs : List Term → Prop
   | [] => True
   | q::qs => NamedOrdinary q ∧ NamedOrdinaryArgs qs
end

/- Original named one-hole typing, with actual literal ordered slots. Binding
is ordinary named binding and is allowed to capture names in the filled hole. -/
inductive NamedContextTyped (S : Signature) : NamedContext → Ty → Ty → Prop where
  | hole : NamedContextTyped S .hole σ σ
  | head : NamedContextTyped S inside σ τ → Admitted S f →
      NamedBase before beforeTypes → NamedValidArgs S before → NamedOrdinaryArgs before →
      NamedBase after afterTypes → NamedValidArgs S after → NamedOrdinaryArgs after →
      f.arguments = beforeTypes ++ τ :: afterTypes →
      NamedContextTyped S (.head f before inside after) σ f.result
  | bind : NamedContextTyped S inside σ τ →
      NamedContextTyped S (.bind name inside) σ (.arrow name.1 τ)

def OrdinaryEncoding : Prop := ∀ env q, NamedOrdinary q ↔ Ordinary (encode env q)
def ContextCoverage : Prop := ∀ S C σ τ, NamedContextTyped S C σ τ →
  ContextTyped S (encodeContext C) σ τ

def NamedWeakContext : Prop := ∀ S C σ τ s t,
  NamedContextTyped S C σ τ → NamedTyped s σ → NamedValid S s → NamedOrdinary s →
  NamedTyped t σ → NamedValid S t → NamedOrdinary t → Weak S (encode [] s) (encode [] t) →
  Weak S (encode [] (namedFill C s)) (encode [] (namedFill C t))
def NamedStrictContext : Prop := ∀ S C σ τ s t,
  NamedContextTyped S C σ τ → NamedTyped s σ → NamedValid S s → NamedOrdinary s →
  NamedTyped t σ → NamedValid S t → NamedOrdinary t → Strict S (encode [] s) (encode [] t) →
  Strict S (encode [] (namedFill C s)) (encode [] (namedFill C t))
end LogicLineages.PersistentMarking.StructuralCoverageTargets
