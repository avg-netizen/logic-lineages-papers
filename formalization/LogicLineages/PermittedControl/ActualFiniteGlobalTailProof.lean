module
public import LogicLineages.PermittedControl.ActualFiniteGlobalTailTargets
import LogicLineages.PermittedControl.ActualFiniteGlobalTailDominanceProof
import LogicLineages.PermittedControl.ActualFiniteGlobalTailEnclosureProof
import LogicLineages.PermittedControl.ActualNodeTailSupplyProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFiniteGlobalTail
open PreparedProjection MixedSameRankResidue
open ActualZeroClassReplacement ActualWeightedReadNormalization ActualZeroClassOutputState
open ActualReadChargeIteration ActualZeroClassCommonTail ActualNodeTailSupply
open SelectedCountOnlyClass (prefixTarget)

private theorem cleanedEdgeLong {f B ρ r zRank source out}
    (edge : ZeroEdge f B ρ r zRank source out) : LongState out := by
  obtain ⟨xs,anns,C,moved,ledger,x₀,q,_,_,_,_,_,_,_,_,_,_,_,_,_,cleaned,_,literal⟩ := edge.actual
  intro rd member
  rw [literal] at member
  exact cleaned.2.2.1 rd member

private theorem traceLiveLong {f B ρ r zRank n initial reached}
    (path : Trace f B ρ r zRank n initial reached) :
    liftedReads f ρ initial.reads → LongState initial →
    liftedReads f ρ reached.reads ∧ LongState reached := by
  induction path with
  | nil s =>
      intro reads long
      exact ⟨reads,long⟩
  | cons head tail ih =>
      intro _ _
      exact ih head.live (cleanedEdgeLong head)

private theorem traceRanks {f B ρ r zRank n initial reached}
    (path : Trace f B ρ r zRank n initial reached) :
    OriginalRanks initial.reads reached.reads := by
  induction path with
  | nil s =>
      intro rd member
      exact ⟨rd,member,rfl⟩
  | cons head tail ih =>
      intro rd member
      obtain ⟨mid,listed,rank⟩ := ih rd member
      obtain ⟨first,prior,same⟩ := head.ranks mid listed
      exact ⟨first,prior,rank.trans same⟩

private theorem labelRank (t : WeightedOperand) (label : PrefixLabel)
    (source : prefixLabel t = some label) : label.rank = t.2.rank := by
  obtain ⟨w,op⟩ := t
  cases op with
  | coordinate rank => cases source
  | ordinary rank field => cases source
  | count rank lam mu =>
      change some (⟨rank,lam,prefixTarget mu⟩ : PrefixLabel) = some label at source
      exact (congrArg PrefixLabel.rank (Option.some.inj source)).symm

theorem exactGlobalGuardSupply : ExactGlobalGuardSupply := by
  intro f B ρ r zRank initial initialReads initialLong payment n reached path xs normalized _
  obtain ⟨live,long⟩ := traceLiveLong path initialReads initialLong
  have sourceRanks := traceRanks path
  have enclosed := exactGlobalLabelEnclosure f B ρ r zRank n initial reached path
  obtain ⟨out,success,_,_,_,_,records⟩ := (exactNormalizedReads f ρ reached.reads).2 live
  have identical : out = xs := Option.some.inj (success.symm.trans normalized)
  subst out
  let terms := xs.map Prod.fst
  let alphabet := globalAlphabet r (syntaxOf initial)
  have covers (t : WeightedOperand) (member : t ∈ terms) : t.2 ∈ alphabet := by
    obtain ⟨rd,retained,tag⟩ := List.mem_map.mp member
    subst t
    obtain ⟨prior,old,key,_⟩ := (records rd retained).2.2
    rw [← key]
    exact enclosed prior old
  have dominated : nodeTail B terms ≤ globalTail B r (syntaxOf initial) :=
    exactAlphabetTailDominance B terms alphabet covers
  have paid : PaidNodeTail B ρ terms := by
    intro label member
    obtain ⟨t,fromTerms,tag⟩ := List.mem_filterMap.mp member
    obtain ⟨rd,retained,eq⟩ := List.mem_map.mp fromTerms
    subst t
    obtain ⟨prior,inSource,op,_⟩ := (records rd retained).2.2
    obtain ⟨first,inOriginal,same⟩ := sourceRanks prior inSource
    have rank : label.rank = first.1.2.rank :=
      (labelRank rd.1 label tag).trans ((congrArg LowerOperand.rank op).symm.trans same)
    rw [rank]
    exact dominated.trans (payment first.1 (List.mem_map.mpr ⟨first,inOriginal,rfl⟩))
  exact (exactNormalizedLongNodeGuards f B ρ reached.reads xs live long normalized paid).2.2

theorem fullActualFiniteGlobalTail : FullActualFiniteGlobalTail :=
  ⟨exactSyntaxCharge,exactGlobalLabelEnclosure,exactAlphabetTailDominance,exactGlobalGuardSupply⟩

end LogicLineages.PermittedControl.ActualFiniteGlobalTail
