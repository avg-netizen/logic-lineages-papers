module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentPermutationReflexivity.InductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentPermutationReflexivity.CoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InductionDefinitions InductionSyntaxProof InductionBindingProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (eqnRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open InternalQuotientComparisonProof InternalBetaTotalityProof

theorem consCore (raw head tail list : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail))) :
    Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) raw list list)) := by
  have ht := atRawApply tail list (belowRawAt raw tail hb (consTailDescent raw head tail hc))
  apply programCases ArgumentEntryCount.count (Fin.cons list (Fin.cons head Fin.elim0)) _
  intro beta j Theta value hj hv
  simp only [consTermRename,emptyRename] at hv
  have hcj := renameInto hc j Theta hj
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hcj htj ⊢
  exact (ArgumentCountComparison.InternalProof.internalCons body beta Theta (raw.relabel j) (head.relabel j)
    (tail.relabel j) (list.relabel j) (list.relabel j) value value hcj hv hv).mpr
    (andIntro ⟨InternalTagArithmeticSupportProof.refl value⟩ htj)

theorem nonzeroAt (raw head list : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head raw))) :
    Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) raw list list)) := by
  apply programCases InternalListCodec.tailCode (Fin.cons raw Fin.elim0) _
  intro beta j Theta tail hj ht
  simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename]
  simp only [consTermRename,emptyRename] at ht
  have hbj := renameInto hb j Theta hj
  rw [belowRawRename] at hbj
  have hnj := renameInto hn j Theta hj
  rw [InternalListCodecDecompositionSupportProof.nonzeroRename] at hnj
  have hhj := renameInto hh j Theta hj
  rw [graph1Rename] at hhj
  exact consCore (raw.relabel j) (head.relabel j) tail (list.relabel j) hbj
    (reconstructNonzero (raw.relabel j) (head.relabel j) tail hnj hhj ht)

theorem nonzeroCore (raw list : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not)) :
    Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) raw list list)) := by
  apply programCases InternalListCodec.headCode (Fin.cons raw Fin.elim0) _
  intro beta j Theta head hj hh
  simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename]
  simp only [consTermRename,emptyRename] at hh
  have hbj := renameInto hb j Theta hj
  rw [belowRawRename] at hbj
  have hnj := renameInto hn j Theta hj
  rw [InternalListCodecDecompositionSupportProof.nonzeroRename] at hnj
  exact nonzeroAt (raw.relabel j) head (list.relabel j) hbj hnj hh

theorem core (raw list : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) raw list list)) := by
  let A := eqn raw z
  apply formulaCases A
  · have hz : Nonempty (Derivation body (A :: Delta) (eqn z raw)) :=
      ⟨InternalTagArithmeticSupportProof.symm (Derivation.hypothesis List.mem_cons_self)⟩
    exact headTransport ArgumentCountComparison.allCounts (numeral 1) z raw (Fin.cons list (Fin.cons list Fin.elim0)) hz
      (ArgumentCountComparison.InternalProof.internalNil body alpha (A :: Delta) list list)
  · exact nonzeroCore raw list (withHyp hb A.not) ⟨Derivation.hypothesis List.mem_cons_self⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentPermutationReflexivity.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentPermutationReflexivity.CoreProof
