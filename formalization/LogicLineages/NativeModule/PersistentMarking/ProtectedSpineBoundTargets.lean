module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineAgreementTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineBoundTargets
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineLaws ProtectedSpineAgreementTargets ProtectedSpineInterpreter
open ProtectedSpineEnvironment (freeCode boundCode)

def BoundImages (E : Environment) (H : List Head) (vs : Args) (removed : List Ty) : Prop :=
  BaseTyped EmptyContext vs removed ∧ ArgsCovered E H vs

def BoundSubstitutionInputs (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (vs : Args) (kept : List Ty) : FrameRelation :=
  fun Γ a b =>
    (∀ σ x, freeCode E Γ a.free σ x = freeCode E Γ b.free σ x) ∧
    (∀ σ i, kept[i]? = some σ → boundCode E Γ a.bound σ i = boundCode E Γ b.bound σ i) ∧
    (∀ i v, vs.get i = some v →
      boundCode E Γ a.bound v.type (kept.length+i) =
        codeAt E v.type (evaluate S E H M v) Γ ⟨b.free,[]⟩)

def RetainedProtection (kept : List Ty) (k l : Nat) : Prop :=
  k = l ∧ k ≤ kept.length

def BoundSubstitution : Prop := ∀ S E H M vs removed kept q σ,
  MarkedConstructorTargets.PrefixClosed E → M ∈ MarkedFamilyCoherence.retained E H →
  BoundImages E H vs removed →
  Typed (BoundContext.prefix kept (BoundContext.prefix removed EmptyContext)) q σ →
  Covered E H q →
  Agreement E σ (evaluate S E H M q) (evaluate S E H M (substitute vs kept.length q))
    (BoundSubstitutionInputs S E H M vs kept) (RetainedProtection kept)

end LogicLineages.PersistentMarking.ProtectedSpineBoundTargets
