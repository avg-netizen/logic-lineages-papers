import LogicLineages.PersistentMarking.FreeVariableRelationSupport
namespace LogicLineages.PersistentMarking.FreeVariableProof
open Spine NameBridge FreeVariableRawSupport FreeVariableRelationSupport

theorem weakAbsent (S : Signature) (s t : Expr) (h : Weak S s t) :
    ∀ name, freeOccurs name s = false → freeOccurs name t = false := by
  apply Weak.rec
    (motive_1 := fun s t _ => ∀ name, freeOccurs name s = false → freeOccurs name t = false)
    (motive_2 := fun s t _ => ∀ name, freeOccurs name s = false → freeOccurs name t = false)
    (motive_3 := fun ss ts _ => ∀ name, freeOccursArgs name ss = false → freeOccursArgs name ts = false)
    (motive_4 := fun ss ts _ => ∀ name, freeOccursArgs name ss = false → freeOccursArgs name ts = false)
    (motive_5 := fun ss ts _ => ∀ name, freeOccursArgs name ss = false → freeOccursArgs name ts = false)
    (motive_6 := fun f base extras qs _ => ∀ name, freeOccurs name (.marked f .ground base extras) = false → freeOccursArgs name qs = false)
    (t := h)
  · intro σ x name hs; exact hs
  · intro σ s τ t x hp ht hxs hxt hw ih name hs
    exact openingTarget name σ x s t hxt ih hs
  · intro f ss g ts hp ht heq htype hm ih name hs
    exact ih name hs
  · intro f ss t hp ht hw ih name hs
    exact ih name (markedAbsent hs rfl)
  · intro f τ ss es t i q domains r hp ht ha hq hcall hw ih name hs
    have harg : freeOccurs name q = false := ha.elim (fun h => atAbsent name h (markedParts hs).1) (fun h => atAbsent name h (markedParts hs).2)
    have hargs := ownerCopiesAbsent name f τ ss es domains hs
    exact ih name (FreeVariableApplicationProof.successfulApplicationAbsence name q _ r harg hargs hcall)
  · intro f σ τ ss es body x hp ht hxo hxb hw ih name hs
    by_cases he : name = (σ,x)
    · subst name; exact hxb
    · have hnew : freeOccurs name (.marked f τ ss (es.append (.cons (.free σ x) .nil))) = false :=
        markedAbsent (markedParts hs).1 (appendAbsent name es _ (markedParts hs).2 (freshSingleton name σ x he))
      exact substituteReflects name (.cons (.free σ x) .nil) 0 body (ih name hnew)
  · intro f ss es g ts hp ht hprec hw ih name hs
    exact ih name hs
  · intro f ss es g ts hp ht heq hm hw ihm ihw name hs
    exact ihw name hs
  · intro q σ t r hp ht hm hw ih name hs
    have hr : freeOccurs name r = false := (ElementarySupportProof.markNames name q r hm).symm.trans hs
    exact ih name hr
  · intro name hs; rfl
  · intro targets y rest x xs hr hw hm ihw ihm name hs
    exact removeAbsent name hr (ihw name (consParts hs).1) (ihm name (consParts hs).2)
  · intro source kept removed target matched added hss hts hn hm hc ihm ihc name hs
    have hp := splitParts name hss hs
    exact splitAbsent name hts (ihm name hp.1) (ihc name hp.2)
  · intro owners name hs; rfl
  · intro owners i q x xs ha he hc ihe ihc name hs
    exact consAbsent (ihe name (atAbsent name ha hs)) (ihc name hs)
  · intro f base extras name hs; rfl
  · intro f base extras q qs hw ht ihw iht name hs
    exact consAbsent (ihw name hs) (iht name hs)

theorem weakContainment : FreeVariableTargets.WeakContainment := by
  intro S s t h name ht
  cases hs : freeOccurs name s with
  | true => rfl
  | false => have hf := weakAbsent S s t h name hs; simp [ht] at hf

theorem strictContainment : FreeVariableTargets.StrictContainment := by
  intro S s t h name ht
  cases h with
  | intro hp htarget hm hw =>
    have hr := weakContainment S _ t hw name ht
    exact (ElementarySupportProof.markNames name _ _ hm).trans hr

theorem fullContainment : FreeVariableTargets.FullContainment := ⟨weakContainment,strictContainment⟩
end LogicLineages.PersistentMarking.FreeVariableProof
