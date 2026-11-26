module
public import LogicLineages.PermittedControl.ActualCanonicalReachedFundingTargets
import LogicLineages.PermittedControl.ActualCanonicalReachedFundingTransferProof
import LogicLineages.PermittedControl.ActualCanonicalReachedFundingTraceProof
import LogicLineages.PermittedControl.ActualCanonicalNormalizedTapeProof
import LogicLineages.PermittedControl.ActualGlobalComparisonCeilingDominanceProof
import LogicLineages.PermittedControl.ActualFullValueLabelsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalReachedFunding
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open ActualFullValueLabels (Label labels ActualLabel exactOriginalReadsHaveFullLabels)
open ActualFiniteFullValueGuards (familyCost ReadyFamily PaidFamily)
open ActualFiniteGlobalTail (syntaxOf globalAlphabet)
open ActualGlobalComparisonCeiling
open ActualCanonicalNormalizedTape

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

theorem exactCanonicalReachedFunding : ExactCanonicalReachedFunding := by
  intro f B hf ρ baseline r top initial reached answers strict agree live ranked long transfer funded path xs normal active
  have ready := exactCanonicalTransferFunding f B hf ρ r top initial reached answers
    live ranked long transfer path xs normal
  let terms := xs.map Prod.fst
  let ls := labels terms
  let alphabet := globalAlphabet r (syntaxOf initial)
  let bound := comparisonCeiling B r (syntaxOf initial)
  obtain ⟨current,_,_,ranks,covered⟩ :=
    exactCanonicalReachFacts f B hf ρ r top initial reached answers live ranked long path
  have tape := exactCanonicalTapeCertificate f ρ reached.reads xs current normal
  have origins := normalizedOrigins f ρ initial.reads reached.reads xs alphabet tape ranks covered
  have sourceScope (t : WeightedOperand) (member : t ∈ syntaxOf initial) : t.2.rank ≤ top := by
    obtain ⟨rd,used,rfl⟩ := List.mem_map.mp member
    exact (ranked rd used).2
  have localTail : familyCost B ls ≤ bound :=
    (exactAlphabetComparisonDominance.1 B terms alphabet (fun t ht => (origins t ht).1)).trans
      (exactAlphabetComparisonDominance.2 B r (syntaxOf initial))
  obtain ⟨actualAnns,_,actualLabels⟩ :=
    exactOriginalReadsHaveFullLabels f B hf ρ terms (xs.map Prod.snd) tape.outputReads ready.1
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
  refine ⟨ready,⟨?_,?_⟩,⟨localTail.trans topPaid,?_⟩⟩
  · intro l used
    obtain ⟨t,ht,eq⟩ := originRank l used
    exact ⟨eq ▸ sourceScope t ht,properFromLabels f ρ actualLabels l used⟩
  · intro l used below
    obtain ⟨t,ht,eq⟩ := originRank l used
    have numeric : bound ≤ ρ l.rank := eq ▸ funded t ht
    rw [agree l.rank below]
    exact localTail.trans numeric
  · intro l used below
    rw [agree l.rank below]
    exact strict below

end LogicLineages.PermittedControl.ActualCanonicalReachedFunding
