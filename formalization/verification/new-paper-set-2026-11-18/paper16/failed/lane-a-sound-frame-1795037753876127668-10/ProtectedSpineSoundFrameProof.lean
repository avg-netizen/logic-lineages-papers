import LogicLineages.PersistentMarking.ProtectedSpineSoundInterpreterTargets
import LogicLineages.PersistentMarking.ProtectedSpineSoundOwnerProof
import LogicLineages.PersistentMarking.ProtectedSpineBoundSyntaxProof
import LogicLineages.PersistentMarking.DecisionSourceSubstitutionProof

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundFrameProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineSoundRelation ProtectedSpineSoundStageTargets
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineSoundInterpreterTargets

theorem boundValid (F : Inputs S) (Γ : Context) {vs : Args} {cs : BoundValues}
    (h : BaseRelated F Γ cs vs) : ProtectedSpineEnvironmentTargets.BoundValid (domain F) Γ cs := by
  induction h with
  | nil => intro a ha; cases ha
  | cons hq _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ProtectedSpineSoundRelationProof.retained F _ _ _ _ hq
    · exact ih a ha

theorem inputs (F : Inputs S) (Γ : Context) (types : List Ty) (vs : Args) (cs : BoundValues)
    (hw : WellFormed F.data.types F.data.ports Γ) (h : Frame F Γ types vs cs) :
    InputValid (domain F) Γ ⟨[],cs⟩ :=
  ⟨hw,by intro p hp; cases hp,boundValid F Γ h.2.2⟩

theorem weakenSources (F : Inputs S) (Γ Δ : Context) (he : Extends Γ Δ) (qs : Args)
    (hq : Sources F Γ qs) : Sources F Δ qs := by
  cases qs with
  | nil => trivial
  | cons q qs =>
    exact ⟨DecisionSourceBasicProof.weakening _ _ _ _ _ _ he hq.1,weakenSources F Γ Δ he qs hq.2⟩
termination_by sizeOf qs

theorem restrict (F : Inputs S) (Γ Δ : Context) (types : List Ty) (vs : Args) (cs : BoundValues)
    (hw : WellFormed F.data.types F.data.ports Γ) (hd : WellFormed F.data.types F.data.ports Δ)
    (he : Extends Γ Δ) (h : Frame F Γ types vs cs) :
    Frame F Δ types vs (weakenBound (domain F) Γ Δ cs) :=
  ⟨h.1,weakenSources F Γ Δ he vs h.2.1,ProtectedSpineSoundOwnerProof.restrictBase F Γ Δ hw hd he h.2.2⟩

theorem lookup (F : Inputs S) (Γ : Context) {vs : Args} {cs : BoundValues}
    (h : BaseRelated F Γ cs vs) (i : Nat) (v : Expr) (hv : vs.get i = some v) :
    Related F v.type Γ (boundCode (domain F) Γ cs v.type i) (some v) := by
  induction h generalizing i with
  | nil => cases hv
  | @cons q c tail qs hq hTail ih =>
    cases i with
    | zero =>
      have hEq : q = v := Option.some.inj hv
      subst v
      simpa [boundCode,lookupBound] using hq
    | succ i =>
      simpa [boundCode,lookupBound] using ih i hv

theorem concreteTyped (types : List Ty) (vs : Args) (hv : BaseTyped EmptyContext vs types)
    (q : Expr) (ht : Typed (BoundContext.prefix types EmptyContext) q q.type) :
    Typed EmptyContext (substitute vs 0 q) q.type :=
  SpineSubstitutionProof.parallelPreserves EmptyContext types vs q q.type hv ht

theorem concreteSource (F : Inputs S) (Γ : Context) (types : List Ty) (vs : Args)
    (q : Expr) (ht : Typed (BoundContext.prefix types EmptyContext) q q.type)
    (hv : BaseTyped EmptyContext vs types) (hu : Source F Γ q) (hvs : Sources F Γ vs) :
    Source F Γ (substitute vs 0 q) :=
  DecisionSourceSubstitutionProof.boundSubstitution _ _ _ _ types vs q q.type ht hv hu hvs

theorem typeTag (types : List Ty) (vs : Args) (hv : BaseTyped EmptyContext vs types)
    (q : Expr) (ht : Typed (BoundContext.prefix types EmptyContext) q q.type) :
    (substitute vs 0 q).type = q.type :=
  SpineShiftProof.annotationExact _ _ _ (concreteTyped types vs hv q ht)

end LogicLineages.PersistentMarking.ProtectedSpineSoundFrameProof
