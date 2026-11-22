module
public import LogicLineages.PermittedControl.ActualCanonicalReachedFundingTargets
import LogicLineages.PermittedControl.ActualCanonicalZeroTraceReplayProof
import LogicLineages.PermittedControl.ActualCanonicalZeroAlphabetProof
import LogicLineages.PermittedControl.ActualFiniteGlobalTailEnclosureProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalReachedFunding
open ActualCanonicalZeroTrace ActualCanonicalZeroAlphabet
open ActualFiniteGlobalTail ActualZeroEdgeAlphabet

private theorem edgeLong {f B ρ r top s t a}
    (edge : CanonicalZeroWitness f B ρ r top s t a) : LongState t := by
  obtain ⟨xs,anns,C,moved,ledger,x₀,q,source,moves,_,_,_,_,_,cleaned,_,output⟩ := edge
  intro rd retained
  rw [output] at retained
  exact cleaned.2.2.1 rd retained

private theorem pathLong {f B ρ r top answers s t}
    (path : CanonicalTrace f B ρ r top answers s t) :
    LongState s → LongState t := by
  induction path with
  | nil s => exact id
  | cons edge path next =>
    intro _
    exact next (edgeLong edge)

theorem exactCanonicalReachFacts : ExactCanonicalReachFacts := by
  intro f B selected ρ r top initial reached answers live ranked long path
  obtain ⟨_,endLive,endRank,origin,_,spent⟩ := exactCanonicalTraceReplay f B selected ρ r top
    initial reached answers path
  have seed : Covers ((syntaxOf initial).map Prod.snd) initial := by
    intro rd member
    exact List.mem_map.mpr ⟨rd.1,List.mem_map.mpr ⟨rd,member,rfl⟩,rfl⟩
  have inside : answers.length < syntaxCharge r (syntaxOf initial) + 1 := by
    rw [exactSyntaxCharge r initial]
    omega
  refine ⟨endLive live,endRank ranked,pathLong path long,origin,?_⟩
  intro rd member
  have covers := exactCanonicalTraceAlphabet f B ρ r top initial reached answers
    ((syntaxOf initial).map Prod.snd) path seed
  exact List.mem_flatMap.mpr ⟨answers.length,List.mem_range.mpr inside,covers rd member⟩

end LogicLineages.PermittedControl.ActualCanonicalReachedFunding
