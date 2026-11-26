import LogicLineages.PersistentMarking.ProtectedSpineSoundHeadProof
import LogicLineages.PersistentMarking.ProtectedSpineSoundSelectProof
import LogicLineages.PersistentMarking.ProtectedSpineSoundFAbsProof
import LogicLineages.PersistentMarking.ProtectedSpineSoundTupleProof
import LogicLineages.PersistentMarking.MarkedConstructorSelectProof
import LogicLineages.PersistentMarking.MarkedConstructorEncodingProof

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundBuilderProof
open Spine DecisionPorts DecisionObservations FiniteDomainFoundation FiniteDomainSchema
open HereditaryDomainCode HereditaryDomainSemantics PortNormalization
open ProtectedSpineAdequacyTargets ProtectedSpineSoundRelation ProtectedSpineSoundStageTargets
open MarkedFamilyParameters (Parameter)
open MarkedConstructorTests (weakTest selectTest copyTest statTest fabsTest)

theorem rootWeak (F : Inputs S) (M : Code) (f : Head) (σ : Ty) (Γ : Context)
    (base : List Code) (extras : List MarkedExtras.Tagged) (bs es : Args) (t : Expr)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (ho : OwnerRelated F (f,σ,Γ,base,extras) bs es) (hM : FamilyRelated F M)
    (hObs : t ∈ observations F.data.names F.data.ports Γ F.target σ)
    (h : weakTest S (domain F) F.data.sourceHeads M (f,σ,Γ,base,extras) t = true) :
    Weak S (.marked f σ bs es) t := by
  let E := domain F
  let H := F.data.sourceHeads
  let p : Parameter := (f,σ,Γ,base,extras)
  simp only [weakTest,Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · exact ProtectedSpineSoundSelectProof.select F M f σ Γ base extras bs es t hm ho hM hObs
      ((MarkedConstructorSelectProof.select E H M p t).mp h)
  · exact ProtectedSpineSoundHeadProof.copy F M f σ Γ base extras bs es t ho hM hObs h
  · exact ProtectedSpineSoundHeadProof.stat F M f σ Γ base extras bs es t ho hM hObs h
  · exact ProtectedSpineSoundFAbsProof.fabs F M f σ Γ base extras bs es t ho hM hObs
      ((MarkedConstructorFAbsExactProof.fabs E H M p t).mp h)

theorem weakAt (F : Inputs S) (M : Code) (p : Parameter) (bs es : Args) (Δ : Context) (t : Expr)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (ho : OwnerRelated F p bs es) (hM : FamilyRelated F M)
    (hd : WellFormed F.data.types F.data.ports Δ) (he : Extends p.2.2.1 Δ)
    (ht : t ∈ observations F.data.names F.data.ports Δ F.target p.2.1)
    (h : (MarkedConstructorValue.build S (domain F) F.data.sourceHeads M p).weak Δ t = true) :
    Weak S (.marked p.1 p.2.1 bs es) t := by
  rcases p with ⟨f,σ,Γ,base,extras⟩
  let w := MarkedFamilyCoherence.weakenParameter (domain F) (f,σ,Γ,base,extras) Δ
  exact rootWeak F M f σ Δ w.2.2.2.1 w.2.2.2.2 bs es t hm
    (ProtectedSpineSoundOwnerProof.weaken F (f,σ,Γ,base,extras) Δ bs es ho hd he) hM ht h

theorem tupleAt (F : Inputs S) (M : Code) (p : Parameter) (bs es : Args) (Δ : Context)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (ho : OwnerRelated F p bs es) (hM : FamilyRelated F M)
    (hd : WellFormed F.data.types F.data.ports Δ) (he : Extends p.2.2.1 Δ)
    (ds : List Ty) (τ : Ty) (hp : (ds,τ) ∈ fullPrefixes p.2.1) (xs : List Code) (args : Args)
    (hx : TupleValues (domain F) Δ ds xs) (hTyped : CallTyped EmptyContext p.2.1 args τ)
    (hSource : Sources F Δ args)
    (hRelated : ∀ i ρ x a, ds[i]? = some ρ → xs[i]? = some x → At args i a → Related F ρ Δ x (some a)) :
    Related F τ Δ ((MarkedConstructorValue.build S (domain F) F.data.sourceHeads M p).application Δ ds τ xs)
      (apply (.marked p.1 p.2.1 bs es) args) := by
  rcases p with ⟨f,σ,Γ,base,extras⟩
  let w := MarkedFamilyCoherence.weakenParameter (domain F) (f,σ,Γ,base,extras) Δ
  exact ProtectedSpineSoundTupleProof.marked F M f σ τ Δ w.2.2.2.1 w.2.2.2.2
    bs es args ds xs hm (ProtectedSpineSoundOwnerProof.weaken F (f,σ,Γ,base,extras) Δ bs es ho hd he)
    hM hp hx hTyped hSource hRelated

theorem build (F : Inputs S) (M : Code) (p : Parameter) (bs es : Args)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (ho : OwnerRelated F p bs es) (hM : FamilyRelated F M) :
    Related F p.2.1 p.2.2.1 (MarkedConstructorOperator.nextFamily S (domain F) F.data.sourceHeads M p)
      (some (.marked p.1 p.2.1 bs es)) := by
  have hEnc := MarkedConstructorEncodingProof.encodeAt S (domain F) F.data.sourceHeads M p
    (ProtectedSpineAdequacyBase.prefixClosed S F) hm ho.1
  rw [Related.eq_def]
  refine ⟨hEnc.1,?_⟩
  intro Δ hd he
  obtain ⟨_,hBits,hApp⟩ := hEnc.2 Δ hd he
  constructor
  · intro t ht
    have hW := weakAt F M p bs es Δ t hm ho hM hd he ht
    have hTarget := ProtectedSpineSoundBitProof.observedPaper F Δ p.2.1 t ht
    obtain ⟨hWeak,hStrict⟩ := hBits t ht
    exact ⟨fun h => hW (hWeak.symm.trans h),
      fun h => .intro ho.2.1 hTarget rfl (hW (hStrict.symm.trans h))⟩
  · intro ds τ hp xs args hx ht hSource hRelated
    rw [hApp ds τ hp xs hx]
    exact tupleAt F M p bs es Δ hm ho hM hd he ds τ hp xs args hx ht hSource hRelated

end LogicLineages.PersistentMarking.ProtectedSpineSoundBuilderProof
