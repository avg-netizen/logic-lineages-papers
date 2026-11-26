module
public import LogicLineages.PermittedControl.ActualGlobalComparisonCeilingTargets
import LogicLineages.PermittedControl.ActualGlobalComparisonCeilingDominanceProof
import LogicLineages.PermittedControl.ActualFiniteGlobalTailEnclosureProof
import LogicLineages.PermittedControl.ActualFiniteGlobalTailProof
import LogicLineages.PermittedControl.ActualFullValueLabelsProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualGlobalComparisonCeiling
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open ActualFullValueLabels (Label labels ActualLabel exactOriginalReadsHaveFullLabels)
open ActualFiniteFullValueGuards (familyCost ReadyFamily PaidFamily)
open ActualFiniteGlobalTail (syntaxOf globalAlphabet exactGlobalLabelEnclosure exactGlobalGuardSupply)
open ActualReadChargeIteration (ReadState Trace NodeGuards ActiveAt)
open ActualZeroClassOutputState (OriginalRanks)
open ActualZeroClassReplacement (Read liftedReads)
open ActualWeightedReadNormalization (normalizeReads exactNormalizedReads)

private theorem traceLive {f B ρ r top n source out}
    (path : Trace f B ρ r top n source out) :
    liftedReads f ρ source.reads → liftedReads f ρ out.reads := by
  induction path with
  | nil s => exact id
  | cons edge tail ih => intro _; exact ih edge.live

private theorem traceRank {f B ρ r top n source out}
    (path : Trace f B ρ r top n source out) : OriginalRanks source.reads out.reads := by
  induction path with
  | nil s => intro rd used; exact ⟨rd,used,rfl⟩
  | cons edge tail ih =>
      intro rd used
      obtain ⟨mid,hm,link⟩ := ih rd used
      obtain ⟨prior,hp,key⟩ := edge.ranks mid hm
      exact ⟨prior,hp,link.trans key⟩

private theorem properFromLabels (f ρ : Nat → Nat) {ls : List Label} {vs : List Nat}
    (actual : List.Forall₂ (ActualLabel f ρ) ls vs) (l : Label) (used : l ∈ ls) :
    ProperField l.field := by
  induction actual with
  | nil => cases used
  | @cons first v ls vs read tail ih =>
      rcases List.mem_cons.mp used with eq | rest
      · subst l
        exact read.1
      · exact ih rest

theorem exactReachedComparisonFamily : ExactReachedComparisonFamily := by
  intro f B hf ρ baseline r top n initial reached strict agree live scoped funded path xs normal active ready
  let terms := xs.map Prod.fst
  let ls := labels terms
  let alphabet := globalAlphabet r (syntaxOf initial)
  let bound := comparisonCeiling B r (syntaxOf initial)
  have covered := exactGlobalLabelEnclosure f B ρ r top n initial reached path
  have ranks := traceRank path
  obtain ⟨ys,hys,_,_,valid,_,records⟩ :=
    (exactNormalizedReads f ρ reached.reads).2 (traceLive path live)
  have same : ys = xs := Option.some.inj (hys.symm.trans normal)
  subst ys
  have origins (t : WeightedOperand) (mem : t ∈ terms) :
      t.2 ∈ alphabet ∧ ∃ original ∈ syntaxOf initial, original.2.rank = t.2.rank := by
    obtain ⟨rd,retained,rfl⟩ := List.mem_map.mp mem
    obtain ⟨prior,old,key,_⟩ := (records rd retained).2.2
    obtain ⟨source,sourceAt,rank⟩ := ranks prior old
    have literal : rd.1.2.rank = source.1.2.rank :=
      (congrArg LowerOperand.rank key).symm.trans rank
    exact ⟨key ▸ covered prior old,source.1,List.mem_map.mpr ⟨source,sourceAt,rfl⟩,literal.symm⟩
  have localTail : familyCost B ls ≤ bound :=
    (exactAlphabetComparisonDominance.1 B terms alphabet (fun t ht => (origins t ht).1)).trans
      (exactAlphabetComparisonDominance.2 B r (syntaxOf initial))
  obtain ⟨actualAnns,_,actualLabels⟩ :=
    exactOriginalReadsHaveFullLabels f B hf ρ terms (xs.map Prod.snd) valid ready.1
  have originRank (l : Label) (used : l ∈ ls) :
      ∃ t ∈ syntaxOf initial, t.2.rank = l.rank := by
    obtain ⟨t,was,_,rank⟩ := labelOrigin terms l used
    obtain ⟨u,hu,same⟩ := (origins t was).2
    exact ⟨u,hu,same.trans rank.symm⟩
  obtain ⟨t,was,_,atTop,_⟩ := active
  obtain ⟨first,inOriginal,originalTop⟩ := (origins t was).2
  have topPaid : bound ≤ ρ top := by
    have uses := funded first inOriginal
    rwa [originalTop,atTop] at uses
  refine ⟨⟨?_,?_⟩,⟨localTail.trans topPaid,?_⟩⟩
  · intro l used
    obtain ⟨t,ht,eq⟩ := originRank l used
    exact ⟨eq ▸ scoped t ht,properFromLabels f ρ actualLabels l used⟩
  · intro l used below
    obtain ⟨t,ht,eq⟩ := originRank l used
    have numeric : bound ≤ ρ l.rank := eq ▸ funded t ht
    rw [agree l.rank below]
    exact localTail.trans numeric
  · intro l used below
    rw [agree l.rank below]
    exact strict below

theorem exactCombinedReachedComparisonSupply : ExactCombinedReachedComparisonSupply := by
  intro f B hf ρ baseline r top n initial reached strict same live long scope tail comparison path xs normal active
  have dynamic := exactGlobalGuardSupply f B ρ r top initial live long tail n reached path xs normal active
  exact ⟨dynamic,exactReachedComparisonFamily f B hf ρ baseline r top n initial reached strict
    same live scope comparison path xs normal active dynamic⟩

end LogicLineages.PermittedControl.ActualGlobalComparisonCeiling
