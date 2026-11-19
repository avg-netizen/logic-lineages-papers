import LogicLineages.PersistentMarking.ProtectedSpineDecisionTargets
import LogicLineages.PersistentMarking.SpineShiftProof

namespace LogicLineages.PersistentMarking.ProtectedSpineDecisionLogicProof
open Spine DecisionRequests PortNormalization
open ProtectedSpineAdequacyTargets ProtectedSpineDecisionTargets

theorem sameType (S : Signature) (q t : Expr) (σ : Ty)
    (hQ : PaperTerm S q σ) (hT : PaperTerm S t σ) :
    q.type = t.type :=
  (SpineShiftProof.annotationExact _ _ _ hQ.1).trans (SpineShiftProof.annotationExact _ _ _ hT.1).symm

theorem weakType (S : Signature) (q t : Expr) (h : Weak S q t) : q.type = t.type := by
  cases h with
  | var => rfl
  | abs hq ht => exact sameType S _ _ _ hq ht
  | funHead hq ht _ he => exact sameType S _ _ _ hq (he.symm ▸ ht)
  | put hq ht => exact sameType S _ _ _ hq ht
  | select hq ht => exact sameType S _ _ _ hq ht
  | fabs hq ht => exact sameType S _ _ _ hq ht
  | copy hq ht => exact sameType S _ _ _ hq ht
  | stat hq ht => exact sameType S _ _ _ hq ht

theorem strictType (S : Signature) (q t : Expr) (h : Strict S q t) : q.type = t.type := by
  cases h with
  | intro hq ht => exact sameType S _ _ _ hq ht

theorem supportExact (s t : Expr) : supportIncluded s t = true ↔ TypeSupport.Included t s := by
  simp only [supportIncluded,TypeSupport.Included,List.all_eq_true,decide_eq_true_eq]

/-- Bridge the literal blank-context value to the original Boolean procedure
without importing any adequacy proof. -/
theorem liftRoot (S : Signature) (F : Inputs S) (he : F.source.type = F.target.type)
    (h : ((FixedValue S F (blank F.data.ports) F.source).weak (blank F.data.ports) F.target = true ↔
        Weak S F.source F.target) ∧
      ((FixedValue S F (blank F.data.ports) F.source).strict (blank F.data.ports) F.target = true ↔
        Strict S F.source F.target)) :
    ((rootBits S F.source F.target).1 = true ↔ Weak S F.source F.target) ∧
      ((rootBits S F.source F.target).2 = true ↔ Strict S F.source F.target) := by
  simp only [rootBits,if_pos he]
  exact h

/-- Factor the unchanged logic of the decision theorem; the only supplier
is the actual same-typed root calculation, discharged in SplitChecks. -/
theorem correctOfSameType
    (same : ∀ S s t σ, PaperTerm S s σ → Ordinary s → PaperTerm S t σ → Ordinary t →
      ((rootBits S s t).1 = true ↔ Weak S s t) ∧
      ((rootBits S s t).2 = true ↔ Strict S s t)) : Decidability := by
  intro S s t σ τ hS hOrdS hT hOrdT
  by_cases he : s.type = t.type
  · have hs := SpineShiftProof.annotationExact _ _ _ hS.1
    have ht := SpineShiftProof.annotationExact _ _ _ hT.1
    have hσ : σ = τ := hs.symm.trans (he.trans ht)
    rw [←hσ] at hT
    obtain ⟨hW,hSt⟩ := same S s t σ hS hOrdS hT hOrdT
    have hDomain : ConfinedPair.Domain S s t := ⟨σ,hS,hT,hOrdS,hOrdT⟩
    refine ⟨hW,hSt,?_,?_⟩
    · simp only [confinedBits,Bool.and_eq_true,hW,supportExact,ConfinedPair.Weak,hDomain,true_and]
    · simp only [confinedBits,Bool.and_eq_true,hSt,supportExact,ConfinedPair.Strict,hDomain,true_and]
  · have hW : ¬ Weak S s t := fun h => he (weakType S s t h)
    have hSt : ¬ Strict S s t := fun h => he (strictType S s t h)
    simp [rootBits,he,confinedBits,ConfinedPair.Weak,ConfinedPair.Strict,hW,hSt]

end LogicLineages.PersistentMarking.ProtectedSpineDecisionLogicProof
