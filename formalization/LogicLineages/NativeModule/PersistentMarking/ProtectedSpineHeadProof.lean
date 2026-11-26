module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineHeadValueProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineHeadProof
open Spine DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineEnvironment ProtectedSpineInterpreterCore ProtectedSpineLaws
open ProtectedSpineHeadParameterProof (parameterAt)
open ProtectedSpineHeadValueProof (headValue)
open MarkedConstructorTargets (PrefixClosed)

def headEvaluation (marked : Bool) (S : Signature) (E : Environment) (heads : List Head) (M : Code)
    (f : Head) (τ : Ty) (base extras : Arguments) : Evaluation where
  value Γ free bound :=
    headValue marked S E heads M (parameterAt E f τ base extras Γ ⟨free,bound⟩)
  nonempty := fun Γ free bound _ d x ds xs υ =>
    let p := parameterAt E f τ base extras Γ ⟨free,bound⟩
    originalHeadCall E heads M Γ f τ p.2.2.2.1 p.2.2.2.2 (d::ds) (x::xs) υ

theorem valueEq (marked : Bool) (S : Signature) (E : Environment) (heads : List Head) (M : Code)
    (f : Head) (τ : Ty) (base extras : Arguments) (Γ : Context) (a : Assignments) :
    valueAt (headEvaluation marked S E heads M f τ base extras) Γ a =
      headValue marked S E heads M (parameterAt E f τ base extras Γ a) := by
  cases a
  rfl

theorem applyEq (marked : Bool) (S : Signature) (E : Environment) (heads : List Head) (M : Code)
    (f : Head) (σ : Ty) (base extras : Arguments) (Γ : Context) (a : Assignments)
    (k : Nat) (ds : List Ty) (τ : Ty) (xs : List Code)
    (hp : MarkedFamilyParameters.Valid E heads (parameterAt E f σ base extras Γ a))
    (hf : (ds,τ) ∈ fullPrefixes σ) (hx : TupleValues E Γ ds xs) :
    nonemptyAt E (headEvaluation marked S E heads M f σ base extras) Γ a k ds τ xs =
      (valueAt (headEvaluation marked S E heads M f σ base extras) Γ a).application Γ ds τ xs := by
  rw [valueEq,ProtectedSpineHeadValueProof.table]
  let p := parameterAt E f σ base extras Γ a
  have he := MarkedConstructorParameterProof.weakenIdentity E heads p hp
  cases ds with
  | nil => exact False.elim ((FinitePrefixProof.forward σ [] τ hf).1 rfl)
  | cons d ds =>
    cases xs with
    | nil => cases hx.1
    | cons x xs =>
      change originalHeadCall E heads M Γ f σ p.2.2.2.1 p.2.2.2.2 (d::ds) (x::xs) τ =
        (MarkedConstructorValue.build S E heads M p).application Γ (d::ds) τ (x::xs)
      simp only [MarkedConstructorValue.build]
      change _ = originalHeadCall E heads M Γ f σ
        (MarkedFamilyCoherence.weakenParameter E p Γ).2.2.2.1
        (MarkedFamilyCoherence.weakenParameter E p Γ).2.2.2.2 (d::ds) (x::xs) τ
      rw [show MarkedFamilyCoherence.weakenParameter E p Γ = p from he]

theorem laws (marked : Bool) (S : Signature) (E : Environment) (heads : List Head) (M : Code)
    (f : Head) (σ : Ty) (base extras : Arguments) (types : List Ty)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E heads)
    (hf : f ∈ heads) (hσ : σ ∈ E.types) (ht : ∀ τ, τ ∈ types → τ ∈ E.types)
    (hl : ArgumentLaws E base f.arguments) (hx : ArgumentLaws E extras types) :
    EvaluationLaws E σ (headEvaluation marked S E heads M f σ base extras) := by
  let p := parameterAt E f σ base extras
  have hp := ProtectedSpineHeadParameterProof.valid E heads f σ base extras types hl hx hf hσ ht
  have hv : ∀ Γ a, InputValid E Γ a →
      Valid E σ Γ (valueAt (headEvaluation marked S E heads M f σ base extras) Γ a) := by
    intro Γ a ha
    rw [valueEq]
    exact ProtectedSpineHeadValueProof.valid marked S E heads M (p Γ a) hc hm (hp Γ a ha)
  have hn : ∀ Γ Δ a, InputValid E Γ a → WellFormed E.types E.ports Δ → Extends Γ Δ →
      ValueEq E σ Δ (valueAt (headEvaluation marked S E heads M f σ base extras) Γ a)
        (valueAt (headEvaluation marked S E heads M f σ base extras) Δ (a.restrict E Γ Δ)) := by
    intro Γ Δ a ha hd he
    rw [valueEq,valueEq]
    have h := ProtectedSpineHeadValueProof.natural marked S E heads M (p Γ a) hc hm (hp Γ a ha) Δ hd he
    have hw := ProtectedSpineHeadParameterProof.natural E f σ base extras types hl hx ht Γ Δ a ha hd he
    rw [hw] at h
    exact h
  refine ⟨hv,hn,?_,?_,?_,?_⟩
  · intro Γ a b ha hb hab
    rw [valueEq,valueEq]
    exact ProtectedSpineHeadValueProof.monotone marked S E heads M (p Γ a) (p Γ b) hc hm
      (hp Γ a ha) (hp Γ b hb)
      (ProtectedSpineHeadParameterProof.ordered E f σ base extras types hl hx ht Γ a b ha hb hab)
  · intro Γ a k ds τ xs ha hpre hxs
    rw [applyEq marked S E heads M f σ base extras Γ a k ds τ xs (hp Γ a ha) hpre hxs]
    exact (hv Γ a ha).1 Γ ha.1 (DecisionPortsProof.extensionRefl Γ) ds τ hpre xs hxs
  · intro Γ Δ a k ds τ xs ha hd he hpre hxs
    have ha' := ProtectedSpineInputProof.restrictValid E Γ Δ a ha hd he
    have hrs : TupleValues E Δ ds (restrictValues E Γ Δ ds xs) :=
      MarkedBaseTupleRestrictionProof.restriction E Γ Δ ds xs ha.1 hd he hxs
    rw [applyEq marked S E heads M f σ base extras Γ a k ds τ xs (hp Γ a ha) hpre hxs,
      applyEq marked S E heads M f σ base extras Δ _ k ds τ _ (hp Δ _ ha') hpre hrs]
    exact ((hv Γ a ha).2.2 Γ Δ ha.1 hd (DecisionPortsProof.extensionRefl Γ) he ds τ hpre xs hxs).trans
      ((hn Γ Δ a ha hd he Δ hd (DecisionPortsProof.extensionRefl Δ)).2.2 ds τ hpre _ hrs)
  · intro Γ a b k ds τ xs ys ha hb hab hpre hxs hys hxy
    rw [applyEq marked S E heads M f σ base extras Γ a k ds τ xs (hp Γ a ha) hpre hxs,
      applyEq marked S E heads M f σ base extras Γ b k ds τ ys (hp Γ b hb) hpre hys,
      valueEq,valueEq,ProtectedSpineHeadValueProof.table,ProtectedSpineHeadValueProof.table]
    exact MarkedConstructorValidityProof.tablesMonotone S E heads M (p Γ a) (p Γ b) Γ ds τ xs ys
      hc hm (hp Γ a ha) (hp Γ b hb)
      (ProtectedSpineHeadParameterProof.ordered E f σ base extras types hl hx ht Γ a b ha hb hab)
      ha.1 (DecisionPortsProof.extensionRefl Γ) hpre hxs hys hxy

end LogicLineages.PersistentMarking.ProtectedSpineHeadProof
