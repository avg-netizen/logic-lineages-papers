module
public import LogicLineages.PermittedControl.ActualCanonicalReachedFundingTargets
import LogicLineages.PermittedControl.ActualCanonicalReachedFundingTraceProof
import LogicLineages.PermittedControl.ActualCanonicalNormalizedTapeProof
import LogicLineages.PermittedControl.ActualFiniteGlobalTailDominanceProof
import LogicLineages.PermittedControl.ActualNodeTailSupplyProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalReachedFunding
open PreparedProjection MixedSameRankResidue
open ActualZeroClassReplacement ActualZeroClassCommonTail ActualNodeTailSupply
open ActualCanonicalNormalizedTape ActualFiniteGlobalTail ActualNormalizedTape ActualZeroEdgeAlphabet
open ActualZeroClassOutputState (OriginalRanks)
open ActualShortCountCleanup
open SelectedCountOnlyClass (prefixTarget)

theorem normalizedOrigins (f ρ : Nat → Nat) (initial reached xs : List Read)
    (alphabet : List LowerOperand) (tape : NormalizedTape f ρ reached xs)
    (ranks : OriginalRanks initial reached) (covered : ∀ rd ∈ reached, rd.1.2 ∈ alphabet) :
    ∀ t : WeightedOperand, t ∈ xs.map Prod.fst →
      t.2 ∈ alphabet ∧ ∃ original ∈ initial.map Prod.fst, original.2.rank = t.2.rank := by
  intro t member
  obtain ⟨rd,retained,rfl⟩ := List.mem_map.mp member
  obtain ⟨prior,old,key,_⟩ := (tape.records rd retained).2.2
  obtain ⟨source,sourceAt,rank⟩ := ranks prior old
  have literal : rd.1.2.rank = source.1.2.rank :=
    (congrArg LowerOperand.rank key).symm.trans rank
  exact ⟨key ▸ covered prior old,source.1,List.mem_map.mpr ⟨source,sourceAt,rfl⟩,literal.symm⟩

private theorem labelRank (t : WeightedOperand) (label : PrefixLabel)
    (source : prefixLabel t = some label) : label.rank = t.2.rank := by
  obtain ⟨w,op⟩ := t
  cases op with
  | coordinate rank => cases source
  | ordinary rank field => cases source
  | count rank lam mu =>
      change some (⟨rank,lam,prefixTarget mu⟩ : PrefixLabel) = some label at source
      exact (congrArg PrefixLabel.rank (Option.some.inj source)).symm

theorem exactCanonicalTransferFunding : ExactCanonicalTransferFunding := by
  intro f B selected ρ r top initial reached answers live ranked long payment path xs normal
  obtain ⟨current,_,currentLong,ranks,covered⟩ :=
    exactCanonicalReachFacts f B selected ρ r top initial reached answers live ranked long path
  have tape := exactCanonicalTapeCertificate f ρ reached.reads xs current normal
  let terms := xs.map Prod.fst
  let alphabet := globalAlphabet r (syntaxOf initial)
  have origins := normalizedOrigins f ρ initial.reads reached.reads xs alphabet tape ranks covered
  have dominated : nodeTail B terms ≤ globalTail B r (syntaxOf initial) :=
    exactAlphabetTailDominance B terms alphabet (fun t used => (origins t used).1)
  have paid : PaidNodeTail B ρ terms := by
    intro label member
    obtain ⟨t,fromTerms,tag⟩ := List.mem_filterMap.mp member
    obtain ⟨first,inOriginal,same⟩ := (origins t fromTerms).2
    have rank := (labelRank t label tag).trans same.symm
    rw [rank]
    exact dominated.trans (payment first inOriginal)
  apply exactLongNodeGuards B ρ xs ?_ paid
  intro t member _
  obtain ⟨rd,retained,rfl⟩ := List.mem_map.mp member
  obtain ⟨prior,old,key,_⟩ := (tape.records rd retained).2.2
  rw [← key]
  exact currentLong prior old

end LogicLineages.PermittedControl.ActualCanonicalReachedFunding
