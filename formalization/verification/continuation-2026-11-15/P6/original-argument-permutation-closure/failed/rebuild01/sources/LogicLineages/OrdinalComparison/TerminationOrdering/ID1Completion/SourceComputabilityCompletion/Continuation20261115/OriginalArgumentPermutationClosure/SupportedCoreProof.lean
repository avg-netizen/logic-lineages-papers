module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.SupportedBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.CoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.SupportedCoreProof
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

open SupportedInductionDefinitions SupportedInductionSyntaxProof SupportedBindingProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (eqnRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open InternalQuotientComparisonProof InternalBetaTotalityProof

open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
theorem consAtCounts (raw left right needle lc rc head tail lh rh : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ha : Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) raw left right)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw needle)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left needle)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc right needle)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hlh : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lh left head)))
    (hrh : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rh right head)))
    : Nonempty (Derivation body Delta (eqn lc rc)) := by
  have hh := (ArgumentCountComparison.InternalProof.internalCons body alpha Delta raw head tail left right lh rh hc hlh hrh).mp ha
  apply formulaCases (eqn head needle)
  · have he : Nonempty (Derivation body (eqn head needle :: Delta) (eqn head needle)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hlq := InternalApplicationValidityStackAppendRunProof.rightTransport ArgumentEntryCount.count lh left head needle he (withHyp hlh _)
    have hrq := InternalApplicationValidityStackAppendRunProof.rightTransport ArgumentEntryCount.count rh right head needle he (withHyp hrh _)
    obtain ⟨hle⟩ := valueUnique ArgumentEntryCount.count lc lh ![left,needle] (withHyp hl _) hlq
    obtain ⟨hre⟩ := valueUnique ArgumentEntryCount.count rc rh ![right,needle] (withHyp hr _) hrq
    obtain ⟨heq⟩ := withHyp (andLeft hh) (eqn head needle)
    exact ⟨trans hle (trans heq (symm hre))⟩
  · have he : Nonempty (Derivation body ((eqn head needle).not :: Delta) (equal head needle).not) := by
      rw [equalEqn]; exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hmt := (PrimaryMembership.Proof.missGraph body alpha ((eqn head needle).not :: Delta) raw head tail needle (numeral 1) (withHyp hc _) he).mp (withHyp hm _)
    exact belowRawApply raw tail left right needle lc rc (withHyp ih _)
      (withHyp (consTailDescent raw head tail hc) _)
      (andIntro (andIntro (andIntro (withHyp (andRight hh) _) hmt) (withHyp hl _)) (withHyp hr _))

theorem atLeft (raw left right needle lc rc head tail lh : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ha : Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) raw left right)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw needle)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left needle)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc right needle)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hlh : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lh left head)))
    : Nonempty (Derivation body Delta (eqn lc rc)) := by
  apply programCases ArgumentEntryCount.count (Fin.cons right (Fin.cons head Fin.elim0)) _
  intro beta j Theta rh hj hx
  rw [eqnRelabel]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hcj
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at haj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hmj
  have hlj := renameInto hl j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hlj
  have hrj := renameInto hr j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hrj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at ihj
  have hlhj := renameInto hlh j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hlhj
  exact consAtCounts (raw.relabel j) (left.relabel j) (right.relabel j) (needle.relabel j) (lc.relabel j) (rc.relabel j) (head.relabel j) (tail.relabel j) (lh.relabel j) rh hcj haj hmj hlj hrj ihj hlhj hx

theorem consCore (raw left right needle lc rc head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ha : Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) raw left right)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw needle)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left needle)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc right needle)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    : Nonempty (Derivation body Delta (eqn lc rc)) := by
  apply programCases ArgumentEntryCount.count (Fin.cons left (Fin.cons head Fin.elim0)) _
  intro beta j Theta lh hj hx
  rw [eqnRelabel]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hcj
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at haj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hmj
  have hlj := renameInto hl j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hlj
  have hrj := renameInto hr j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hrj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at ihj
  exact atLeft (raw.relabel j) (left.relabel j) (right.relabel j) (needle.relabel j) (lc.relabel j) (rc.relabel j) (head.relabel j) (tail.relabel j) lh hcj haj hmj hlj hrj ihj hx

theorem nonzeroAt (raw left right needle lc rc head : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) raw left right)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw needle)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left needle)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc right needle)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hz : Nonempty (Derivation body Delta ((eqn raw z).not)))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head raw)))
    : Nonempty (Derivation body Delta (eqn lc rc)) := by
  apply programCases InternalListCodec.tailCode (Fin.cons raw Fin.elim0) _
  intro beta j Theta tail hj hx
  rw [eqnRelabel]
  simp only [consTermRename,emptyRename] at hx
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at haj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hmj
  have hlj := renameInto hl j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hlj
  have hrj := renameInto hr j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hrj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at ihj
  have hzj := renameInto hz j Theta hj
  change Nonempty (Derivation body Theta ((eqn raw z).relabel j).not) at hzj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hzj
  have hhj := renameInto hh j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hhj
  exact consCore (raw.relabel j) (left.relabel j) (right.relabel j) (needle.relabel j) (lc.relabel j) (rc.relabel j) (head.relabel j) tail
    (reconstructNonzero (raw.relabel j) (head.relabel j) tail hzj hhj hx) haj hmj hlj hrj ihj

theorem nonzeroCore (raw left right needle lc rc : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) raw left right)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw needle)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left needle)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc right needle)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hz : Nonempty (Derivation body Delta ((eqn raw z).not)))
    : Nonempty (Derivation body Delta (eqn lc rc)) := by
  apply programCases InternalListCodec.headCode (Fin.cons raw Fin.elim0) _
  intro beta j Theta head hj hx
  rw [eqnRelabel]
  simp only [consTermRename,emptyRename] at hx
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at haj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hmj
  have hlj := renameInto hl j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hlj
  have hrj := renameInto hr j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hrj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at ihj
  have hzj := renameInto hz j Theta hj
  change Nonempty (Derivation body Theta ((eqn raw z).relabel j).not) at hzj
  simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hzj
  exact nonzeroAt (raw.relabel j) (left.relabel j) (right.relabel j) (needle.relabel j) (lc.relabel j) (rc.relabel j) head haj hmj hlj hrj ihj hzj hx

theorem core (raw left right needle lc rc : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) raw left right)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw needle)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left needle)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc right needle)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    : Nonempty (Derivation body Delta (eqn lc rc)) := by
  apply formulaCases (eqn raw z)
  · have he : Nonempty (Derivation body (eqn raw z :: Delta) (eqn raw z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hm0 := headTransport contains (numeral 1) raw z (Fin.cons needle Fin.elim0) he (withHyp hm _)
    have hz := (PrimaryMembership.Proof.nilGraph body alpha (eqn raw z :: Delta) (numeral 1) needle).mp hm0
    rw [equalEqn] at hz
    obtain ⟨hz⟩ := hz
    exact ⟨Derivation.explosion (sucNeZeroApply hz)⟩
  · exact nonzeroCore raw left right needle lc rc (withHyp ha _) (withHyp hm _) (withHyp hl _) (withHyp hr _) (withHyp ih _) ⟨Derivation.hypothesis List.mem_cons_self⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.SupportedCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.SupportedCoreProof
