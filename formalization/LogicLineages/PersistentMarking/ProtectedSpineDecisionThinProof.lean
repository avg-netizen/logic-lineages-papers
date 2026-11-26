import LogicLineages.PersistentMarking.ProtectedSpineDecisionTargets
import LogicLineages.PersistentMarking.ProtectedSpineAdequacyThinChecks
import LogicLineages.PersistentMarking.DecisionClosureInitialProof

namespace LogicLineages.PersistentMarking.ProtectedSpineDecisionThinProof
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

theorem exact_Decidability : Decidability := by
  intro S s t σ τ hS hOrdS hT hOrdT
  by_cases he : s.type = t.type
  · have hs := SpineShiftProof.annotationExact _ _ _ hS.1
    have ht := SpineShiftProof.annotationExact _ _ _ hT.1
    have hσ : σ = τ := hs.symm.trans (he.trans ht)
    rw [←hσ] at hT
    let F : Inputs S := ⟨s,t,σ,σ,hS,hT,hOrdS,hOrdT⟩
    let Γ := blank F.data.ports
    have hRoot := (DecisionClosureInitialProof.initial S F).1
    have hAdequacy := ProtectedSpineAdequacyThinChecks.exact_ExactObservation S F Γ s t σ
      hRoot.1 hRoot.2.1 hRoot.2.2 hS hT
    have hW : (rootBits S s t).1 = true ↔ Weak S s t := by
      simp only [rootBits,if_pos he]
      exact hAdequacy.1
    have hSt : (rootBits S s t).2 = true ↔ Strict S s t := by
      simp only [rootBits,if_pos he]
      exact hAdequacy.2
    have hDomain : ConfinedPair.Domain S s t := ⟨σ,hS,hT,hOrdS,hOrdT⟩
    refine ⟨hW,hSt,?_,?_⟩
    · simp only [confinedBits,Bool.and_eq_true,hW,supportExact,ConfinedPair.Weak,hDomain,true_and]
    · simp only [confinedBits,Bool.and_eq_true,hSt,supportExact,ConfinedPair.Strict,hDomain,true_and]
  · have hW : ¬ Weak S s t := fun h => he (weakType S s t h)
    have hSt : ¬ Strict S s t := fun h => he (strictType S s t h)
    simp [rootBits,he,confinedBits,ConfinedPair.Weak,ConfinedPair.Strict,hW,hSt]

#print axioms exact_Decidability
end LogicLineages.PersistentMarking.ProtectedSpineDecisionThinProof
