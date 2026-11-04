module
public import LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectCarrierTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectCarrierProof
open Source QuotientDirectCarrier NumberedNumericCarrier NumberedQuotientPaths

theorem listCarrier : QuotientDirectCarrierTargets.ActualListCarrier := by
  intro n arity symbols S hc Gamma values
  simp only [listCarrierTest,List.all_eq_true]
  constructor
  · intro h x hx
    exact (NumberedNumericCarrierProof.canonicalCarrierTestCorrect n arity symbols S hc Gamma x).mp (h x hx)
  · intro h x hx
    exact (NumberedNumericCarrierProof.canonicalCarrierTestCorrect n arity symbols S hc Gamma x).mpr (h x hx)

theorem positivePathCarrier : QuotientDirectCarrierTargets.ActualPositivePathCarrier := by
  intro n arity symbols S hc Gamma table x y h
  induction h with
  | step he =>
    obtain ⟨certificate,ht⟩ :=
      (NumberedNumericQuotientEdgeProof.numericQuotientEdge n arity symbols S Gamma table _ _).mpr he
    exact NumberedNumericQuotientEdgeProof.numericEdgeCarrier n arity symbols S hc Gamma table _ _ certificate ht
  | trans h1 h2 ih1 ih2 => exact ⟨ih1.1,ih2.2⟩

theorem directCarrierPreservation : QuotientDirectCarrierTargets.ActualDirectCarrierPreservation := by
  intro n arity symbols S hc Gamma table source target h hsource
  obtain ⟨kept,removed,inserted,hs,ht,_,hd⟩ := h
  simp only [listCarrierTest,List.all_eq_true] at hsource ⊢
  intro y hy
  rcases List.mem_append.mp (ht.mem_iff.mp hy) with hkeep | hins
  · exact hsource y (hs.mem_iff.mpr (List.mem_append.mpr (Or.inl hkeep)))
  · obtain ⟨z,_,hr⟩ := hd y hins
    exact (positivePathCarrier n arity symbols S hc Gamma table z y hr).2

end LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectCarrierProof
