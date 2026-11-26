module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalScanInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalScanProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalTransparentMinimum OriginalTransparentMinimumInternalScanSyntaxProof
open OriginalTransparentMinimumInternalScanInductionProof
open InternalGraphComposition InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalOriginalOrderSyntaxProof InternalSquareRootArithmeticSupportProof
open InternalQuotientComparisonProof InternalPositiveUnfoldingSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalTransparentMinimumInternalScan :
    OriginalTransparentMinimumTargets.ActualOriginalTransparentMinimumInternalScan := by
  intro Q body α Delta out bound seed parameter earlier
  let A := graph3 (scan Q) out bound seed parameter
  obtain ⟨h⟩ := rowApply Q bound seed parameter out earlier
    (allRows (body := body) (Gamma := A :: Delta) Q bound)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  let E := eqn out bound ⊓ ltF earlier bound
  have hm : Derivation body (E :: A :: Delta) (graph3 Q (suc z) seed earlier parameter).not := by
    have he : Derivation body (E :: A :: Delta) (eqn out bound) :=
      Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)
    have hl : Derivation body (E :: A :: Delta) (ltF earlier bound) :=
      Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)
    exact Derivation.implicationElimination
      (addHyp (Derivation.conjunctionRight (Derivation.conjunctionRight h)) _)
      (orderRight earlier (symm he) hl)
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.conjunctionLeft h) (Derivation.conjunctionIntroduction
      (Derivation.conjunctionLeft (Derivation.conjunctionRight h))
      (Derivation.conjunctionIntroduction
        (Derivation.conjunctionRight (Derivation.conjunctionRight h))
        (Derivation.implicationIntroduction (by
          simpa only [E,A,InternalControlGraphSupportProof.equalEqn,
            InternalLessThan.strictLess,InternalOriginalOrderSyntaxProof.ltF,
            InternalOriginalStepGuard.one] using hm)))))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalScanProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalScanProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalScanProof.actualOriginalTransparentMinimumInternalScan
