module
public import LogicLineages.OrdinalComparison.ComparisonNodeProgramProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonNode

theorem natural_sign_swap (a b c d : Nat) (h : comparisonNaturalSign a b=comparisonNaturalSign c d) :
    comparisonNaturalSign b a=comparisonNaturalSign d c := by
  have hl : b<a ↔ d<c := by
    rw [←(natural_sign a b).2.2.2,←(natural_sign c d).2.2.2,h]
  have hr : a<b ↔ c<d := by
    rw [←(natural_sign a b).2.1,←(natural_sign c d).2.1,h]
  unfold comparisonNaturalSign
  simp only [hl,hr]

theorem point_tail_from_stable (E F : OneVariableComparisonExpr)
    (hE : oneVariableComparisonValid E) (hF : oneVariableComparisonValid F)
    (N : Nat) (hN : 1≤N) (hEN : oneVariableComparisonDomainBound E≤N) (hFN : oneVariableComparisonDomainBound F≤N)
    (hstable : ∀ x : Nat,N≤x →
      comparisonNaturalSign (actualOneVariableComparisonValue E x) (actualOneVariableComparisonValue F x)=
        comparisonNaturalSign (actualOneVariableComparisonValue E N) (actualOneVariableComparisonValue F N)) :
    comparisonEventualSignData E F
      (encodedSourcePairSignAt (oneVariableComparisonEncode E) (oneVariableComparisonEncode F) N,N) := by
  have hpoint := point_program.2.2 E F hE hF N hEN hFN
  have hsign : encodedSourcePairSignAt (oneVariableComparisonEncode E) (oneVariableComparisonEncode F) N=
      comparisonNaturalSign (actualOneVariableComparisonValue E N) (actualOneVariableComparisonValue F N) := by
    unfold encodedSourcePairSignAt
    rw [((OneVariableComparison.source_program.2.2 E hE).2.2 N hEN).2,
      ((OneVariableComparison.source_program.2.2 F hF).2.2 N hFN).2]
  refine ⟨hpoint.1,hN,?_⟩
  intro x hx
  refine ⟨((OneVariableComparison.source_program.2.2 E hE).2.2 x (hEN.trans hx)).1,
    ((OneVariableComparison.source_program.2.2 F hF).2.2 x (hFN.trans hx)).1,?_⟩
  rw [hsign,←hstable x hx]
  exact (natural_sign _ _).2

end LogicLineages.OrdinalComparison.ComparisonNode
