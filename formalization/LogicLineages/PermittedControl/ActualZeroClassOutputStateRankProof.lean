module
public import LogicLineages.PermittedControl.ActualZeroClassOutputStateTargets
import LogicLineages.PermittedControl.ActualZeroClassCommonTailProof
import LogicLineages.PermittedControl.ActualZeroClassCohortTransferMinimumProof
import LogicLineages.PermittedControl.ActualZeroClassOutsideAndShiftComplementProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassOutputState
open PreparedProjection MixedSameRankResidue
open ActualZeroClassReplacement ActualWeightedReadNormalization ActualZeroClassCohortTransfer
open ActualZeroClassRecombinedRow ActualCountOriginDispositions ActualZeroClassOutsideAndShift
open ActualZeroClassCommonTail
open SelectedCountOnlyClass (prefixTarget)

private theorem emittedAtAnchor (f ρ : Nat → Nat) (a : SurvivingPrefix)
    (ps : List SurvivingPrefix) (out : List Read) (moves : MovedPrefixes f ρ a ps out) :
    ∀ rd ∈ out, rd.1.2.rank = a.rank := by
  induction moves with
  | nil => simp
  | same _ _ _ ih =>
      intro rd member
      rcases List.mem_cons.mp member with rfl | later
      · rfl
      · exact ih rd later
  | higher _ _ _ _ ih =>
      intro rd member
      rcases List.mem_cons.mp member with rfl | later
      · rfl
      · rcases List.mem_cons.mp later with rfl | later
        · rfl
        · exact ih rd later

private theorem labelRank (t : WeightedOperand) (l : PrefixLabel) (found : prefixLabel t = some l) :
    l.rank = t.2.rank := by
  obtain ⟨w, op⟩ := t
  cases op with
  | coordinate rank => cases found
  | ordinary rank F => cases found
  | count rank lam mu =>
      change some (⟨rank,lam,prefixTarget mu⟩ : PrefixLabel) = some l at found
      exact (congrArg PrefixLabel.rank (Option.some.inj found)).symm

theorem exactOutputRankProvenance : ExactOutputRankProvenance := by
  classical
  intro f ρ C raw xs annotations moved paid normalized
  dsimp only
  intro aligned moves
  let terms := xs.map Prod.fst
  let ps := cohort f C terms annotations
  let outside := outsideCohort f C terms (xs.map Prod.snd) annotations
  obtain ⟨found, success, _, _, _, _, records⟩ := (exactNormalizedReads f ρ raw).2 paid
  have identical : found = xs := Option.some.inj (success.symm.trans normalized)
  subst found
  have source (rd : Read) (member : rd ∈ xs) :
      ∃ prior ∈ raw, rd.1.2.rank = prior.1.2.rank := by
    obtain ⟨prior, old, key, _⟩ := (records rd member).2.2
    exact ⟨prior,old,(congrArg LowerOperand.rank key).symm⟩
  have kept := exactOutsideClass f ρ C raw xs annotations paid normalized aligned
  change MovedAt f ρ (leastPrefix ps) ps moved at moves
  change OriginalRanks raw (outside ++ moved)
  intro rd member
  rcases List.mem_append.mp member with untouched | emitted
  · change rd ∈ outsideCohort f C terms (xs.map Prod.snd) annotations at untouched
    rw [kept] at untouched
    exact source rd (List.mem_filter.mp untouched).1
  · cases chosen : leastPrefix ps with
    | none =>
        rw [chosen] at moves
        exact False.elim (List.not_mem_nil (moves.2 ▸ emitted))
    | some a =>
        rw [chosen] at moves
        have anchorRank := emittedAtAnchor f ρ a ps moved moves rd emitted
        have anchorMember := (exactLeastPrefix.2 ps a chosen).1
        have present := exactCohortLabelProvenance f C terms annotations a anchorMember
        obtain ⟨t,fromTerms,tag⟩ := List.mem_filterMap.mp present
        obtain ⟨retained,inXs,termEq⟩ := List.mem_map.mp fromTerms
        subst t
        obtain ⟨prior, inRaw, same⟩ := source retained inXs
        exact ⟨prior,inRaw,anchorRank.trans ((labelRank retained.1 (survivorLabel a) tag).trans same)⟩

end LogicLineages.PermittedControl.ActualZeroClassOutputState
