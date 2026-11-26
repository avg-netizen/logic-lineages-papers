module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentPairProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentSelectorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (suc z eqn)
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalTagArithmeticSyntaxProof (sucRelabel)
open InternalUnpairReverseBoundsArithmeticProof (weakTrans)
open InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof (emptyRename)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalPairingSumBounds (weakBound)
open ObservationDescentDefinitions ObservationDescentPairProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualSelectorBound : ObservationDescentTargets.ActualSelectorBound := by
 intro path
 induction path with
 | nil =>
   intro body alpha Delta input selected h
   obtain ⟨he⟩ := valueUnique (.projection (0 : Fin 1)) selected input (Fin.cons input Fin.elim0)
     h (projectionValue 0 (Fin.cons input Fin.elim0))
   exact ⟨InternalQuotientComparisonProof.equalToNext he⟩
 | cons b ps ih =>
   intro body alpha Delta input selected h
   let P : Program 1 := if b then InternalUnpair.right else InternalUnpair.left
   apply programCases P (Fin.cons input Fin.elim0) _
   intro beta j Theta mid hj hm
   simp only [weakBound,InternalLessThan.strictLess,orderRename,sucRelabel]
   simp only [consTermRename,emptyRename] at hm
   have h' := renameInto h j Theta hj
   simp only [graph1,programRename,consTermRename,emptyRename] at h'
   have hs := unaryRecover (select ps) P (selected.relabel j) mid
     (Fin.cons (input.relabel j) Fin.elim0) h' hm
   have hb : Nonempty (Derivation body Theta (weakBound mid (input.relabel j))) := by
     cases b with
     | false => exact leftBound (input.relabel j) mid hm
     | true => exact rightBound (input.relabel j) mid hm
   exact weakTrans (selected.relabel j) mid (input.relabel j)
     (ih body beta Theta mid (selected.relabel j) hs) hb
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentSelectorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentSelectorProof
