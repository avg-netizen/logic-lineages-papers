module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.RebuildBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.CoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.CountAgreementBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.RebuildCoreProof
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

open RebuildInductionDefinitions RebuildInductionSyntaxProof RebuildBindingProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (eqnRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open InternalQuotientComparisonProof InternalBetaTotalityProof

open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open CountAgreement CountAgreementSyntaxProof CountAgreementBindingProof
theorem consAtCounts (raw left right head tail lc rc : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ha : Nonempty (Derivation body Delta (agreement left right)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left head)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc right head)))
    : Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) raw left right)) := by
  have htail := belowRawApply raw tail left right ih (consTailDescent raw head tail hc) ha
  exact (ArgumentCountComparison.InternalProof.internalCons body alpha Delta raw head tail left right lc rc hc hl hr).mpr
    (andIntro (agreementApply left right head lc rc ha hl hr) htail)

theorem atLeft (raw left right head tail lc : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ha : Nonempty (Derivation body Delta (agreement left right)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left head)))
    : Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) raw left right)) := by
  apply programCases ArgumentEntryCount.count (Fin.cons right (Fin.cons head Fin.elim0)) _
  intro beta j Theta rc hj hx
  simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,agreementRename,RebuildInductionSyntaxProof.belowRawRename] at hcj
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,agreementRename,RebuildInductionSyntaxProof.belowRawRename] at haj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,agreementRename,RebuildInductionSyntaxProof.belowRawRename] at ihj
  have hlj := renameInto hl j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,agreementRename,RebuildInductionSyntaxProof.belowRawRename] at hlj
  exact consAtCounts (raw.relabel j) (left.relabel j) (right.relabel j) (head.relabel j) (tail.relabel j) (lc.relabel j) rc hcj haj ihj hlj hx

theorem consCore (raw left right head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ha : Nonempty (Derivation body Delta (agreement left right)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    : Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) raw left right)) := by
  apply programCases ArgumentEntryCount.count (Fin.cons left (Fin.cons head Fin.elim0)) _
  intro beta j Theta lc hj hx
  simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,agreementRename,RebuildInductionSyntaxProof.belowRawRename] at hcj
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,agreementRename,RebuildInductionSyntaxProof.belowRawRename] at haj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,agreementRename,RebuildInductionSyntaxProof.belowRawRename] at ihj
  exact atLeft (raw.relabel j) (left.relabel j) (right.relabel j) (head.relabel j) (tail.relabel j) lc hcj haj ihj hx

theorem nonzeroAt (raw left right head : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (agreement left right)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hz : Nonempty (Derivation body Delta ((eqn raw z).not)))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head raw)))
    : Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) raw left right)) := by
  apply programCases InternalListCodec.tailCode (Fin.cons raw Fin.elim0) _
  intro beta j Theta tail hj hx
  simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename]
  simp only [consTermRename,emptyRename] at hx
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,agreementRename,RebuildInductionSyntaxProof.belowRawRename] at haj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,agreementRename,RebuildInductionSyntaxProof.belowRawRename] at ihj
  have hzj := renameInto hz j Theta hj
  change Nonempty (Derivation body Theta ((eqn raw z).relabel j).not) at hzj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,agreementRename,RebuildInductionSyntaxProof.belowRawRename] at hzj
  have hhj := renameInto hh j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,agreementRename,RebuildInductionSyntaxProof.belowRawRename] at hhj
  exact consCore (raw.relabel j) (left.relabel j) (right.relabel j) (head.relabel j) tail
    (reconstructNonzero (raw.relabel j) (head.relabel j) tail hzj hhj hx) haj ihj

theorem nonzeroCore (raw left right : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (agreement left right)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hz : Nonempty (Derivation body Delta ((eqn raw z).not)))
    : Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) raw left right)) := by
  apply programCases InternalListCodec.headCode (Fin.cons raw Fin.elim0) _
  intro beta j Theta head hj hx
  simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename]
  simp only [consTermRename,emptyRename] at hx
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,agreementRename,RebuildInductionSyntaxProof.belowRawRename] at haj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,agreementRename,RebuildInductionSyntaxProof.belowRawRename] at ihj
  have hzj := renameInto hz j Theta hj
  change Nonempty (Derivation body Theta ((eqn raw z).relabel j).not) at hzj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,agreementRename,RebuildInductionSyntaxProof.belowRawRename] at hzj
  exact nonzeroAt (raw.relabel j) (left.relabel j) (right.relabel j) head haj ihj hzj hx

theorem core (raw left right : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (agreement left right)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    : Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) raw left right)) := by
  apply formulaCases (eqn raw z)
  · have he : Nonempty (Derivation body (eqn raw z :: Delta) (eqn z raw)) := ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩
    exact headTransport ArgumentCountComparison.allCounts (numeral 1) z raw (Fin.cons left (Fin.cons right Fin.elim0)) he
      (ArgumentCountComparison.InternalProof.internalNil body alpha (eqn raw z :: Delta) left right)
  · exact nonzeroCore raw left right (withHyp ha _) (withHyp ih _) ⟨Derivation.hypothesis List.mem_cons_self⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.RebuildCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.RebuildCoreProof
