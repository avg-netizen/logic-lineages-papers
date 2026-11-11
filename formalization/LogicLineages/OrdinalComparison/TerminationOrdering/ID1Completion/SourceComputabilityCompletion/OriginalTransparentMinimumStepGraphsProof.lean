module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumStepGraphsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalTransparentMinimum
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalAcceptanceBranchProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalEqualityTestCompositionProof InternalEqualityTestProof InternalLessThanSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof
open InternalBetaTotalityProof InternalPositiveUnfoldingSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

def stepXs (index previous seed parameter : OTerm α) : Fin 4 → OTerm α :=
  Fin.cons index (Fin.cons previous (Fin.cons seed (Fin.cons parameter Fin.elim0)))

theorem stepLess (out index previous seed parameter : OTerm α)
    (h : Nonempty (Derivation body Delta (lessGraph out previous index))) :
    Nonempty (Derivation body Delta
      (programGraph (.composition InternalLessThan.ltTest ![.projection 1,.projection 0]) out
        (stepXs index previous seed parameter))) := by
  apply compositionValue InternalLessThan.ltTest ![.projection 1,.projection 0] out
    (stepXs index previous seed parameter) (Fin.cons previous (Fin.cons index Fin.elim0)) h
  intro i
  exact Fin.cases (projectionValue 1 _) (Fin.cases (projectionValue 0 _) (fun j => Fin.elim0 j)) i

theorem stepQuery (Q : Program 3) (out index previous seed parameter : OTerm α)
    (h : Nonempty (Derivation body Delta (graph3 Q out seed index parameter))) :
    Nonempty (Derivation body Delta
      (programGraph (.composition Q ![.projection 2,.projection 0,.projection 3]) out
        (stepXs index previous seed parameter))) := by
  apply compositionValue Q ![.projection 2,.projection 0,.projection 3] out
    (stepXs index previous seed parameter) (Fin.cons seed (Fin.cons index (Fin.cons parameter Fin.elim0))) h
  intro i
  exact Fin.cases (projectionValue 2 _)
    (Fin.cases (projectionValue 0 _) (Fin.cases (projectionValue 3 _) (fun j => Fin.elim0 j))) i

theorem stepEquality (Q : Program 3) (out value index previous seed parameter : OTerm α)
    (hq : Nonempty (Derivation body Delta (graph3 Q value seed index parameter)))
    (he : Nonempty (Derivation body Delta (equalityGraph out value (suc z)))) :
    Nonempty (Derivation body Delta
      (programGraph (.composition InternalEqualityTest.equalityTest
        ![.composition Q ![.projection 2,.projection 0,.projection 3],InternalLessThan.constantOne 4])
        out (stepXs index previous seed parameter))) := by
  apply compositionValue InternalEqualityTest.equalityTest _ out (stepXs index previous seed parameter)
    (Fin.cons value (Fin.cons (suc z) Fin.elim0)) he
  intro i
  exact Fin.cases (stepQuery Q value index previous seed parameter hq)
    (Fin.cases (oneConstantValue _) (fun j => Fin.elim0 j)) i

theorem stepRetained (Q : Program 3) (index previous seed parameter : OTerm α)
    (h : Nonempty (Derivation body Delta (InternalLessThan.strictLess previous index))) :
    Nonempty (Derivation body Delta
      (programGraph (scanStep Q) previous (stepXs index previous seed parameter))) := by
  apply successorBranchIntro _ _ _ previous z (stepXs index previous seed parameter)
    (stepLess (suc z) index previous seed parameter (acceptOfLess previous index h))
  exact projectionValue 1 _

theorem stepHit (Q : Program 3) (index previous seed parameter : OTerm α)
    (h : Nonempty (Derivation body Delta (InternalLessThan.strictLess previous index).not))
    (hq : Nonempty (Derivation body Delta (graph3 Q (suc z) seed index parameter))) :
    Nonempty (Derivation body Delta
      (programGraph (scanStep Q) index (stepXs index previous seed parameter))) := by
  apply zeroBranchIntro _ _ _ index (stepXs index previous seed parameter)
    (stepLess z index previous seed parameter (rejectOfNotLess previous index h))
  apply successorBranchIntro _ _ _ index z (stepXs index previous seed parameter)
    (stepEquality Q (suc z) (suc z) index previous seed parameter hq
      (equalityOfEqual (suc z) (suc z) ⟨refl _⟩))
  exact projectionValue 0 _

theorem equalityRejected (x y : OTerm α)
    (hn : Nonempty (Derivation body Delta (eqn x y).not)) :
    Nonempty (Derivation body Delta (equalityGraph z x y)) := by
  obtain ⟨hn⟩ := hn
  obtain ⟨cmp⟩ := actualOriginalComparison body α x y
  have hc := compareView (weakenClosed cmp Delta)
  obtain ⟨hl⟩ := rejectForwardOrder (body := body) (Gamma := ltF x y :: Delta) x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have he : Derivation body Delta ((eqn x y).imp (equalityGraph z x y)) :=
    Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination (addHyp hn _) (Derivation.hypothesis List.mem_cons_self)))
  obtain ⟨hr⟩ := rejectBackwardOrder (body := body) (Gamma := ltF y x :: Delta) x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hrest : Derivation body Delta ((eqn x y ⊔ ltF y x).imp (equalityGraph z x y)) :=
    Derivation.implicationIntroduction (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp he _) (addHyp (Derivation.implicationIntroduction hr) _))
  exact ⟨disjunctionElimination hc (Derivation.implicationIntroduction hl) hrest⟩

theorem stepMissAtValue (Q : Program 3) (value index previous seed parameter : OTerm α)
    (h : Nonempty (Derivation body Delta (InternalLessThan.strictLess previous index).not))
    (hq : Nonempty (Derivation body Delta (graph3 Q value seed index parameter)))
    (hn : Nonempty (Derivation body Delta (eqn value (suc z)).not)) :
    Nonempty (Derivation body Delta
      (programGraph (scanStep Q) (suc index) (stepXs index previous seed parameter))) := by
  apply zeroBranchIntro _ _ _ (suc index) (stepXs index previous seed parameter)
    (stepLess z index previous seed parameter (rejectOfNotLess previous index h))
  apply zeroBranchIntro _ _ _ (suc index) (stepXs index previous seed parameter)
    (stepEquality Q z value index previous seed parameter hq (equalityRejected value (suc z) hn))
  apply compositionValue .succ (fun _ : Fin 1 => .projection 0) (suc index)
    (stepXs index previous seed parameter) (Fin.cons index Fin.elim0) (successorValue _)
  intro i
  exact Fin.cases (projectionValue 0 _) (fun j => Fin.elim0 j) i

theorem stepMiss (Q : Program 3) (index previous seed parameter : OTerm α)
    (h : Nonempty (Derivation body Delta (InternalLessThan.strictLess previous index).not))
    (hn : Nonempty (Derivation body Delta (graph3 Q (suc z) seed index parameter).not)) :
    Nonempty (Derivation body Delta
      (programGraph (scanStep Q) (suc index) (stepXs index previous seed parameter))) := by
  apply programCases Q (Fin.cons seed (Fin.cons index (Fin.cons parameter Fin.elim0))) _
  intro β j Gamma value hj hq
  have h' := renameInto h j Gamma hj
  have hn' := renameInto hn j Gamma hj
  simp only [programRename,stepXs,consTermRename,emptyRename,sucRelabel]
  simp only [InternalLessThan.strictLess,InternalOriginalOrderSyntaxProof.orderRename] at h'
  simp only [graph3,programRename,consTermRename,emptyRename,sucRelabel,zRelabel] at hn'
  have he : Nonempty (Derivation body Gamma (eqn value (suc z)).not) := by
    obtain ⟨ht⟩ := outputTransport Q value (suc z)
      (fun i => ((Fin.cons seed (Fin.cons index (Fin.cons parameter Fin.elim0))) i).relabel j)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hq _)
    obtain ⟨hn'⟩ := hn'
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (addHyp hn' _) ht)⟩
  exact stepMissAtValue Q value (index.relabel j) (previous.relabel j) (seed.relabel j)
    (parameter.relabel j) h' hq he

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumStepGraphsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumStepGraphsProof
