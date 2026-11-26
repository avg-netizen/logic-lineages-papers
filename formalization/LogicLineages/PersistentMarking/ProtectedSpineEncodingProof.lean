import LogicLineages.PersistentMarking.ProtectedSpineInputProof

namespace LogicLineages.PersistentMarking.ProtectedSpineEncodingProof
open Spine DecisionPorts HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineLaws
open ProtectedSpineInterpreterCore (Evaluation)

theorem encodeAt (E : Environment) (σ : Ty) (ev : Evaluation) (hl : EvaluationLaws E σ ev)
    (Γ : Context) (a : Assignments) (ha : InputValid E Γ a) :
    codeAt E σ ev Γ a ∈ (descriptor E σ).carriers Γ ∧
    ValueEq E σ Γ (decode E σ Γ (codeAt E σ ev Γ a)) (valueAt ev Γ a) :=
  HereditaryEncodeDecodeProof.encodeDecode E σ Γ _ ha.1 (hl.valid Γ a ha)

theorem codeNatural (E : Environment) (σ : Ty) (ev : Evaluation) (hl : EvaluationLaws E σ ev)
    (Γ Δ : Context) (a : Assignments) (ha : InputValid E Γ a)
    (hd : WellFormed E.types E.ports Δ) (he : Extends Γ Δ) :
    (descriptor E σ).restrict Γ Δ (codeAt E σ ev Γ a) = codeAt E σ ev Δ (a.restrict E Γ Δ) := by
  have hΓ := encodeAt E σ ev hl Γ a ha
  have hΔ := encodeAt E σ ev hl Δ (a.restrict E Γ Δ) (ProtectedSpineInputProof.restrictValid E Γ Δ a ha hd he)
  have hr := HereditaryRestrictionProof.restriction E σ Γ Δ ha.1 hd he _ hΓ.1
  exact HereditaryEncodingCongruenceProof.injective E σ Δ _ _ hr.1 hΔ.1
    (HereditaryValueEqualityProof.trans hr.2
      (HereditaryValueEqualityProof.trans (HereditaryValueEqualityProof.weaken he hΓ.2)
        (HereditaryValueEqualityProof.trans (hl.natural Γ Δ a ha hd he)
          (HereditaryValueEqualityProof.symm hΔ.2))))

theorem codeOrder (E : Environment) (σ : Ty) (ev : Evaluation) (hl : EvaluationLaws E σ ev)
    (Γ : Context) (a b : Assignments) (ha : InputValid E Γ a) (hb : InputValid E Γ b)
    (hab : InputLE E Γ a b) :
    (descriptor E σ).le Γ (codeAt E σ ev Γ a) (codeAt E σ ev Γ b) = true := by
  have hA := encodeAt E σ ev hl Γ a ha
  have hB := encodeAt E σ ev hl Γ b hb
  exact (HereditaryCodeOrderProof.exactOrder E σ Γ _ _ ha.1 hA.1 hB.1).mpr
    (HereditaryValueEqualityProof.order (HereditaryValueEqualityProof.symm hA.2)
      (HereditaryValueEqualityProof.symm hB.2) (hl.monotone Γ a b ha hb hab))

end LogicLineages.PersistentMarking.ProtectedSpineEncodingProof
