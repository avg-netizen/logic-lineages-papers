module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineBoundSyntaxProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineFreeInputProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineFrameAgreementProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineBoundInputProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineLaws ProtectedSpineInterpreter ProtectedSpineBoundTargets
open ProtectedSpineEnvironment
open MarkedConstructorTargets (PrefixClosed)

theorem getFacts (E : Environment) (H : List Head) (vs : Args)
    (ht : ExtrasTyped EmptyContext vs) (hc : ArgsCovered E H vs) (i : Nat) (v : Expr)
    (hv : vs.get i = some v) : Typed EmptyContext v v.type ∧ Covered E H v := by
  cases vs with
  | nil => cases hv
  | cons q qs =>
    cases ht with
    | cons hq hqs =>
      obtain ⟨ha,hb⟩ := ProtectedSpineCoverageProof.argumentCons E H q qs hc
      cases i with
      | zero =>
        have he : q = v := Option.some.inj hv
        subst v
        exact ⟨(SpineShiftProof.annotationExact _ _ _ hq).symm ▸ hq,ha⟩
      | succ i => exact getFacts E H qs hqs hb i v hv
termination_by sizeOf vs

theorem weaken (S : Signature) (E : Environment) (H : List Head) (M : Code) (vs : Args)
    (removed kept : List Ty) (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (hv : BoundImages E H vs removed) (Γ Δ : Context)
    (a b : Assignments) (ha : InputValid E Γ a) (hb : InputValid E Γ b)
    (hr : BoundSubstitutionInputs S E H M vs kept Γ a b)
    (hd : WellFormed E.types E.ports Δ) (he : Extends Γ Δ) :
    BoundSubstitutionInputs S E H M vs kept Δ (a.restrict E Γ Δ) (b.restrict E Γ Δ) := by
  have hs := ProtectedSpineFrameAgreementProof.weaken E (fun i => kept[i]?) Γ Δ a b
    ha hb ⟨hr.1,hr.2.1⟩ hd he
  refine ⟨hs.1,hs.2,?_⟩
  intro i v hi
  obtain ⟨hTyped,hCovered⟩ := getFacts E H vs (DecisionOccurrenceProof.baseExtras _ _ _ hv.1) hv.2 i v hi
  let ev := evaluate S E H M v
  have hl := ProtectedSpineInterpretationProof.laws S E H M hc hm EmptyContext v v.type hTyped hCovered
  have hL := (ProtectedSpineEnvironmentNaturalProof.lookupWeakening
    E Γ Δ a.free a.bound v.type 0 (kept.length+i) ha.1 hd he ha.2.1 ha.2.2).2.symm
  rw [hr.2.2 i v hi] at hL
  have hR := ProtectedSpineEncodingProof.codeNatural E v.type ev hl Γ Δ ⟨b.free,[]⟩
      (ProtectedSpineFreeInputProof.emptyBoundValid E Γ b hb) hd he
  exact hL.trans hR

theorem push (S : Signature) (E : Environment) (H : List Head) (M : Code) (vs : Args)
    (kept : List Ty) (Γ : Context) (a b : Assignments) (σ : Ty) (c : Code)
    (h : BoundSubstitutionInputs S E H M vs kept Γ a b) :
    BoundSubstitutionInputs S E H M vs (σ::kept) Γ (a.push σ c) (b.push σ c) := by
  refine ⟨h.1,?_,?_⟩
  · intro τ i hi
    cases i with
    | zero => simp [Assignments.push,boundCode,lookupBound]
    | succ i => simpa [Assignments.push,boundCode,lookupBound] using h.2.1 τ i hi
  · intro i v hi
    have he : (σ::kept).length+i = (kept.length+i)+1 := by simp; omega
    rw [he]
    simpa [Assignments.push,boundCode,lookupBound] using h.2.2 i v hi

end LogicLineages.PersistentMarking.ProtectedSpineBoundInputProof
