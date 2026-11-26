module
public import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetTargets
import LogicLineages.PermittedControl.ActualZeroClassCommonTailProof
import LogicLineages.PermittedControl.ActualZeroClassCohortTransferMinimumProof
import LogicLineages.PermittedControl.ActualZeroClassOutsideAndShiftComplementProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroEdgeAlphabet
open PreparedProjection MixedSameRankResidue ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualZeroClassCommonTail ActualZeroClassCohortTransfer ActualCountOriginDispositions
open ActualZeroClassRecombinedRow ActualZeroClassOutsideAndShift
open ActualShortCountCleanup ActualReadChargeIteration

private theorem originalIn (alphabet : List LowerOperand) (key : LowerOperand)
    (member : key ∈ alphabet) : key ∈ expand alphabet := by
  exact List.mem_append.mpr (Or.inl member)

private theorem prefixIn (alphabet : List LowerOperand) (l : PrefixLabel)
    (member : l ∈ prefixCandidates alphabet) : prefixOperand l ∈ expand alphabet := by
  exact List.mem_append.mpr (Or.inr (List.mem_append.mpr
    (Or.inl (List.mem_map.mpr ⟨l,member,rfl⟩))))

private theorem pairIn (alphabet : List LowerOperand) (lo hi : PrefixLabel)
    (loMem : lo ∈ prefixCandidates alphabet) (hiMem : hi ∈ prefixCandidates alphabet)
    (ordered : lo.rank < hi.rank) : pairOperand lo hi ∈ expand alphabet := by
  apply List.mem_append.mpr
  right
  apply List.mem_append.mpr
  right
  change pairOperand lo hi ∈ pairCandidates (prefixCandidates alphabet)
  apply List.mem_flatMap.mpr
  refine ⟨lo,loMem,List.mem_map.mpr ⟨hi,?_,rfl⟩⟩
  exact List.mem_filter.mpr ⟨hiMem,decide_eq_true ordered⟩

private theorem prefixIgnoresWeight (t : WeightedOperand) : prefixLabel t = prefixLabel (1,t.2) := by
  obtain ⟨w,op⟩ := t
  cases op <;> rfl

private theorem movedIn (f ρ : Nat → Nat) (a : SurvivingPrefix) (ps : List SurvivingPrefix)
    (out : List Read) (alphabet : List LowerOperand)
    (moves : MovedPrefixes f ρ a ps out) (anchor : survivorLabel a ∈ prefixCandidates alphabet) :
    (∀ p ∈ ps, survivorLabel p ∈ prefixCandidates alphabet) →
    ∀ rd ∈ out, rd.1.2 ∈ expand alphabet := by
  induction moves with
  | nil => simp
  | @same p ps tail _ _ _ ih =>
      intro candidates rd member
      rcases List.mem_cons.mp member with rfl | later
      · exact prefixIn alphabet (survivorLabel a) anchor
      · exact ih (fun q hq => candidates q (List.mem_cons_of_mem _ hq)) rd later
  | @higher p ps tail i strict _ _ _ ih =>
      intro candidates rd member
      rcases List.mem_cons.mp member with rfl | later
      · exact prefixIn alphabet (survivorLabel a) anchor
      · rcases List.mem_cons.mp later with rfl | later
        · exact pairIn alphabet (survivorLabel a) (survivorLabel p) anchor
            (candidates p List.mem_cons_self) strict
        · exact ih (fun q hq => candidates q (List.mem_cons_of_mem _ hq)) rd later

theorem exactZeroEdgeAlphabet : ExactZeroEdgeAlphabet := by
  classical
  intro f B ρ r zRank source out alphabet edge original
  obtain ⟨xs,annotations,C,moved,ledger,x₀,q,norm,_,_,chosenClass,_,_,_,move,_,_,_,_,_,_,_,outReads⟩ :=
    edge.actual
  have paid : liftedReads f ρ source.reads := by
    by_contra unpaid
    have failure := (exactNormalizedReads f ρ source.reads).1.mpr unpaid
    rw [norm] at failure
    cases failure
  obtain ⟨found, success, _, _, _, _, records⟩ := (exactNormalizedReads f ρ source.reads).2 paid
  have identical : found = xs := Option.some.inj (success.symm.trans norm)
  subst found
  have normIn (rd : Read) (member : rd ∈ xs) : rd.1.2 ∈ alphabet := by
    obtain ⟨prior,old,key,_⟩ := (records rd member).2.2
    rw [← key]
    exact original prior old
  let terms := xs.map Prod.fst
  let ps := cohort f C terms annotations
  let outside := outsideCohort f C terms (xs.map Prod.snd) annotations
  have outsideExact := exactOutsideClass f ρ C source.reads xs annotations paid norm chosenClass.1
  have cohortIn (p : SurvivingPrefix) (member : p ∈ ps) :
      survivorLabel p ∈ prefixCandidates alphabet := by
    have hit := exactCohortLabelProvenance f C terms annotations p member
    obtain ⟨t,listed,key⟩ := List.mem_filterMap.mp hit
    obtain ⟨rd,observed,eq⟩ := List.mem_map.mp listed
    subst t
    exact List.mem_filterMap.mpr ⟨rd.1.2,normIn rd observed,(prefixIgnoresWeight rd.1).symm.trans key⟩
  change MovedAt f ρ (leastPrefix ps) ps moved at move
  change out.reads = retained (outside ++ moved) at outReads
  intro rd member
  rw [outReads] at member
  have live : rd ∈ outside ++ moved := (List.mem_filter.mp member).1
  rcases List.mem_append.mp live with untouched | emitted
  · change rd ∈ outsideCohort f C terms (xs.map Prod.snd) annotations at untouched
    rw [outsideExact] at untouched
    exact originalIn alphabet rd.1.2 (normIn rd (List.mem_filter.mp untouched).1)
  · cases selected : leastPrefix ps with
    | none =>
        rw [selected] at move
        exact False.elim (List.not_mem_nil (move.2 ▸ emitted))
    | some a =>
        rw [selected] at move
        exact movedIn f ρ a ps moved alphabet move
          (cohortIn a (exactLeastPrefix.2 ps a selected).1) cohortIn rd emitted

theorem exactTraceAlphabet : ExactTraceAlphabet := by
  intro f B ρ r zRank n source out path
  induction path with
  | nil s => exact ⟨by simp,fun _ covers => covers⟩
  | @cons n s t u head tail ih =>
      obtain ⟨spent,continues⟩ := ih
      have strict := head.strict
      refine ⟨by omega,?_⟩
      intro alphabet covers
      exact continues (expand alphabet) (exactZeroEdgeAlphabet f B ρ r zRank s t alphabet head covers)

theorem fullActualZeroEdgeAlphabet : FullActualZeroEdgeAlphabet :=
  ⟨exactZeroEdgeAlphabet,exactTraceAlphabet⟩

end LogicLineages.PermittedControl.ActualZeroEdgeAlphabet
