module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceCompletenessTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceCompletenessProof
open RankedPrecedenceCertificate RankedPrecedenceCompleteness

theorem memLower {n : Nat} (table : Fin n → Fin n → Bool) (f g : Fin n) :
    g ∈ lowerSet table f ↔ table f g = true := by
  simp [lowerSet]

theorem lowerCardBound {n : Nat} (table : Fin n → Fin n → Bool) (h : StrictTotalTable table) (f : Fin n) :
    (lowerSet table f).card < n := by
  have hs : lowerSet table f ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _,?_⟩
    intro he
    have hm : f ∈ lowerSet table f := he.symm ▸ Finset.mem_univ f
    have ht := (memLower table f f).mp hm
    rw [h.1 f] at ht
    cases ht
  simpa using Finset.card_lt_card hs

theorem lowerCardDecrease {n : Nat} (table : Fin n → Fin n → Bool) (h : StrictTotalTable table)
    (f g : Fin n) (hfg : table f g = true) : (lowerSet table g).card < (lowerSet table f).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_,?_⟩
  · intro k hk
    exact (memLower table f k).mpr (h.2.1 f g k hfg ((memLower table g k).mp hk))
  · intro he
    have hg : g ∈ lowerSet table g := he.symm ▸ (memLower table f g).mpr hfg
    have ht := (memLower table g g).mp hg
    rw [h.1 g] at ht
    cases ht

theorem actualRankCertificateExistence : RankedPrecedenceCompletenessTargets.ActualRankCertificateExistence := by
  intro n table
  constructor
  · rintro ⟨rank,h⟩
    exact RankedPrecedenceCertificateProof.actualRankedStrictOrder n table rank h
  · intro h
    let rank : Fin n → Fin n := fun f => ⟨(lowerSet table f).card,lowerCardBound table h f⟩
    have hi : Function.Injective rank := by
      intro f g he
      by_contra hn
      have hv : (lowerSet table f).card = (lowerSet table g).card := congrArg Fin.val he
      rcases h.2.2 f g hn with hfg | hgf
      · have hd := lowerCardDecrease table h f g hfg; omega
      · have hd := lowerCardDecrease table h g f hgf; omega
    refine ⟨rank,(RankedPrecedenceCertificateProof.actualRankCertificateTest n table rank).mpr ⟨hi,?_⟩⟩
    intro f g
    constructor
    · intro hfg
      exact lowerCardDecrease table h f g hfg
    · intro hlt
      by_cases he : f = g
      · subst g
        exact False.elim ((Nat.lt_irrefl _) hlt)
      · rcases h.2.2 f g he with hfg | hgf
        · exact hfg
        · have hd := lowerCardDecrease table h g f hgf
          change (lowerSet table g).card < (lowerSet table f).card at hlt
          omega

theorem actualSymbolCycleExclusion : RankedPrecedenceCompletenessTargets.ActualSymbolCycleExclusion := by
  intro n table h length values hpos hedge he
  obtain ⟨rank,hr⟩ := (actualRankCertificateExistence n table).mpr h
  have hb := (RankedPrecedenceChainsProof.actualSymbolChainBound n table rank hr length values hedge).1
  rw [he] at hb
  omega

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceCompletenessProof
