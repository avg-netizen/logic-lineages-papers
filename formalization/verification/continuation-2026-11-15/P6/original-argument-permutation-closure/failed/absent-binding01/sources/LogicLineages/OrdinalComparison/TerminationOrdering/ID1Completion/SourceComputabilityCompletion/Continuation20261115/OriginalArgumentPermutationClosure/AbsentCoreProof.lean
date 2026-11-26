module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.AbsentBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.CoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.AbsentCoreProof
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

open AbsentInductionDefinitions AbsentInductionSyntaxProof AbsentBindingProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (eqnRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open InternalQuotientComparisonProof InternalBetaTotalityProof

open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
theorem headAbsent (raw head tail needle : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hn : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw needle).not)) :
    Nonempty (Derivation body Delta (eqn head needle).not) := by
  have hh := containsHit raw head tail needle (withHyp hc (eqn head needle))
    (by rw [equalEqn]; exact ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hh⟩ := hh
  obtain ⟨hn⟩ := hn
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _) hh)⟩

theorem tailAbsent (raw head tail needle : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hn : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw needle).not)) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) tail needle).not) := by
  let A := graph2 contains (numeral 1) tail needle
  have he := withHyp (headAbsent raw head tail needle hc hn) A
  have hh := containsMiss raw head tail needle (numeral 1) (withHyp hc A)
    (by simpa only [equalEqn] using he) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hh⟩ := hh
  obtain ⟨hn⟩ := hn
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _) hh)⟩

theorem consAtCount (raw head tail needle count tailCount : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hn : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw needle).not))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count count raw needle)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count tailCount tail needle))) :
    Nonempty (Derivation body Delta (eqn count z)) := by
  obtain ⟨hz⟩ := belowRawApply raw tail needle tailCount ih (consTailDescent raw head tail hc)
    (andIntro (tailAbsent raw head tail needle hc hn) ht)
  have hp := ArgumentEntryCount.InternalProof.internalUnequalCons body alpha Delta raw head tail needle tailCount hc ht
    (headAbsent raw head tail needle hc hn)
  obtain ⟨he⟩ := valueUnique ArgumentEntryCount.count count tailCount ![raw,needle] hv hp
  exact ⟨trans he hz⟩

theorem consCore (raw head tail needle count : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hn : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw needle).not))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count count raw needle)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (eqn count z)) := by
  apply programCases ArgumentEntryCount.count (Fin.cons tail (Fin.cons needle Fin.elim0)) _
  intro beta j Theta tailCount hj ht
  simp only [eqnRelabel,InternalTagArithmeticSyntaxProof.zRelabel]
  simp only [consTermRename,emptyRename] at ht
  have hcj := renameInto hc j Theta hj
  rw [graph2Rename] at hcj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((graph2 contains (numeral 1) raw needle).relabel j).not) at hnj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hvj := renameInto hv j Theta hj
  rw [graph2Rename] at hvj
  have ihj := renameInto ih j Theta hj
  rw [belowRawRename] at ihj
  exact consAtCount (raw.relabel j) (head.relabel j) (tail.relabel j) (needle.relabel j) (count.relabel j) tailCount hcj hnj hvj ihj ht

theorem nonzeroAt (raw needle count head : OTerm alpha)
    (hn : Nonempty (Derivation body Delta ((graph2 contains (numeral 1) raw needle).not)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count count raw needle)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hz : Nonempty (Derivation body Delta ((eqn raw z).not)))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head raw)))
    : Nonempty (Derivation body Delta (eqn count z)) := by
  apply programCases InternalListCodec.tailCode (Fin.cons raw Fin.elim0) _
  intro beta j Theta tail hj hx
  simp only [eqnRelabel,InternalTagArithmeticSyntaxProof.zRelabel]
  simp only [consTermRename,emptyRename] at hx
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((graph2 contains (numeral 1) raw needle).relabel j).not) at hnj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hnj
  have hvj := renameInto hv j Theta hj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hvj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at ihj
  have hzj := renameInto hz j Theta hj
  change Nonempty (Derivation body Theta ((eqn raw z).relabel j).not) at hzj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hzj
  have hhj := renameInto hh j Theta hj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hhj
  exact consCore (raw.relabel j) (head.relabel j) tail (needle.relabel j) (count.relabel j)
    (reconstructNonzero (raw.relabel j) (head.relabel j) tail hzj hhj hx) hnj hvj ihj

theorem nonzeroCore (raw needle count : OTerm alpha)
    (hn : Nonempty (Derivation body Delta ((graph2 contains (numeral 1) raw needle).not)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count count raw needle)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hz : Nonempty (Derivation body Delta ((eqn raw z).not)))
    : Nonempty (Derivation body Delta (eqn count z)) := by
  apply programCases InternalListCodec.headCode (Fin.cons raw Fin.elim0) _
  intro beta j Theta head hj hx
  simp only [eqnRelabel,InternalTagArithmeticSyntaxProof.zRelabel]
  simp only [consTermRename,emptyRename] at hx
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((graph2 contains (numeral 1) raw needle).relabel j).not) at hnj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hnj
  have hvj := renameInto hv j Theta hj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hvj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at ihj
  have hzj := renameInto hz j Theta hj
  change Nonempty (Derivation body Theta ((eqn raw z).relabel j).not) at hzj
  simp only [graph1Rename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,belowRawRename] at hzj
  exact nonzeroAt (raw.relabel j) (needle.relabel j) (count.relabel j) head hnj hvj ihj hzj hx

theorem core (raw needle count : OTerm alpha)
    (hn : Nonempty (Derivation body Delta ((graph2 contains (numeral 1) raw needle).not)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count count raw needle)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    : Nonempty (Derivation body Delta (eqn count z)) := by
  apply formulaCases (eqn raw z)
  · have he : Nonempty (Derivation body (eqn raw z :: Delta) (eqn raw z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hv0 := headTransport ArgumentEntryCount.count count raw z (Fin.cons needle Fin.elim0) he (withHyp hv _)
    exact valueUnique ArgumentEntryCount.count count z ![z,needle] hv0
      (ArgumentEntryCount.InternalProof.internalNil body alpha (eqn raw z :: Delta) needle)
  · exact nonzeroCore raw needle count (withHyp hn _) (withHyp hv _) (withHyp ih _) ⟨Derivation.hypothesis List.mem_cons_self⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.AbsentCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.AbsentCoreProof
