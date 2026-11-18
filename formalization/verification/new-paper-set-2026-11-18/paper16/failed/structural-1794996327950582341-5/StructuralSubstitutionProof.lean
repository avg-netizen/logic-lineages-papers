import LogicLineages.PersistentMarking.StructuralStabilityTargets
import LogicLineages.PersistentMarking.TwoEnvironmentProof
import LogicLineages.PersistentMarking.ConservativeProof
import LogicLineages.PersistentMarking.AuxiliaryEmbeddingProof
import LogicLineages.PersistentMarking.ElementaryProof
namespace LogicLineages.PersistentMarking.StructuralSubstitutionProof
open Spine StructuralStabilityTargets

mutual
 theorem shiftOrdinary (a d : Nat) (q : Expr) (h : Ordinary q) : Ordinary (shift a d q) := by
  cases q with
  | free σ x => trivial
  | bound σ i => trivial
  | lam σ q => exact shiftOrdinary a (d+1) q h
  | head f qs => exact shiftOrdinaryArgs a d qs h
  | marked f τ qs es => exact h.elim
 termination_by sizeOf q
 theorem shiftOrdinaryArgs (a d : Nat) (qs : Args) (h : OrdinaryArgs qs) : OrdinaryArgs (shiftArgs a d qs) := by
  cases qs with
  | nil => trivial
  | cons q qs => exact ⟨shiftOrdinary a d q h.1,shiftOrdinaryArgs a d qs h.2⟩
 termination_by sizeOf qs
end
mutual
 theorem ordinary (θ : FreeMap) (ho : ∀ σ x, Ordinary (θ σ x)) (d : Nat) (q : Expr)
    (h : Ordinary q) : Ordinary (freeSub θ d q) := by
  cases q with
  | free σ x => exact shiftOrdinary d 0 (θ σ x) (ho σ x)
  | bound σ i => trivial
  | lam σ q => exact ordinary θ ho (d+1) q h
  | head f qs => exact ordinaryArgs θ ho d qs h
  | marked f τ qs es => exact h.elim
 termination_by sizeOf q
 theorem ordinaryArgs (θ : FreeMap) (ho : ∀ σ x, Ordinary (θ σ x)) (d : Nat) (qs : Args)
    (h : OrdinaryArgs qs) : OrdinaryArgs (freeSubArgs θ d qs) := by
  cases qs with
  | nil => trivial
  | cons q qs => exact ⟨ordinary θ ho d q h.1,ordinaryArgs θ ho d qs h.2⟩
 termination_by sizeOf qs
end

theorem related (S : Signature) (θ : FreeMap) (h : OrdinaryMap S θ) : TwoEnvironmentTargets.Related S θ θ := by
  intro σ x
  exact AuxiliaryEmbeddingProof.embedWeak S _ _
    (ElementaryProof.ordinaryReflexive S (θ σ x) σ (h σ x).1 (h σ x).2)

theorem weakMarked (S : Signature) (s t : Expr) (θ : FreeMap)
    (ho : Ordinary t) (hθ : OrdinaryMap S θ) (h : Weak S s t) :
    Weak S (freeSub θ 0 s) (freeSub θ 0 t) := by
  have ht : FreeMapTyped EmptyContext θ := fun σ x => (hθ σ x).1.1
  have he := TwoEnvironmentProof.weak S θ θ ht ht (related S θ hθ) s t
    (AuxiliaryEmbeddingProof.embedWeak S s t h)
  obtain ⟨tree⟩ := he
  have hp := (ExtendedEndpointProof.weakFacts tree).1
  exact ConservativeProof.weak S _ _ _
    (AuxiliaryReflexivityProof.refinementRefl S _ _ hp) ⟨tree⟩
    (ordinary θ (fun σ x => (hθ σ x).2) 0 t ho)

theorem weakSubstitution : WeakSubstitution := by
  intro S s t θ _ ht hθ h
  exact weakMarked S s t θ ht hθ h

theorem strictSubstitution : StrictSubstitution := by
  intro S s t θ _ ht hθ h
  cases h with
  | intro hs hp hm hw =>
    have hmap : FreeMapTyped EmptyContext θ := fun σ x => (hθ σ x).1.1
    have hvalid := fun σ x => (hθ σ x).1.2
    exact .intro (RefinementSubstitutionSupport.subPaper S θ hmap hvalid _ _ hs)
      (RefinementSubstitutionSupport.subPaper S θ hmap hvalid _ _ hp)
      (SpineMarkingProof.covariance θ 0 _ _ hm) (weakMarked S _ _ θ ht hθ hw)
end LogicLineages.PersistentMarking.StructuralSubstitutionProof
