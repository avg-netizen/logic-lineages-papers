module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNonConsCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTailCoherence.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesOrderedAnswers.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.NilSuppliersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.LeafSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNonConsCoherence.StepProof
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
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel eqnRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)

open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open InternalAcceptanceBranchProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open OriginalRawSyntaxTransport (constant)
def caseFormula (six : Bool) (tag : OTerm alpha) : Formula alpha :=
  if six then eqn tag (numeral 6) else (eqn tag (numeral 6)).not

theorem caseRename (six : Bool) (tag : OTerm alpha) {beta : Type} (j : alpha → beta) :
    (caseFormula six tag).relabel j = caseFormula six (tag.relabel j) := by
  cases six <;> simp only [caseFormula, Bool.false_eq_true, ↓reduceIte, eqnRelabel, GuardedSourceSyntaxProof.numeralRename]

theorem canonicalStep (six : Bool) (raw tag tail : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (hn : Nonempty (Derivation body Delta (eqn tag (numeral 7)).not))
    (hc : Nonempty (Derivation body Delta (caseFormula six tag))) :
    Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.step (numeral (if six then 1 else 0)) raw tail)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons tail Fin.elim0)
  have htag : Nonempty (Derivation body Delta (programGraph (leftOf ArgumentEntriesLayer.raw) tag xs)) :=
    unaryValue InternalUnpair.left ArgumentEntriesLayer.raw tag raw xs ht (projectionValue 0 xs)
  cases six with
  | true =>
    have he : Nonempty (Derivation body Delta (eqn tag (numeral 6))) := hc
    have h6 := outputTransport (leftOf ArgumentEntriesLayer.raw) tag (numeral 6) xs he htag
    exact branchNumeralIntro 6 6 (leftOf ArgumentEntriesLayer.raw) _ _ (numeral 1) xs h6
      (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 1 xs)
  | false =>
    have h6 : Nonempty (Derivation body Delta (equal tag (numeral 6)).not) := by
      simpa only [equalEqn] using hc
    have h7 : Nonempty (Derivation body Delta (equal tag (numeral 7)).not) := by
      simpa only [equalEqn] using hn
    have hz6 := sameReject (leftOf ArgumentEntriesLayer.raw) (constant 2 6) tag (numeral 6) xs htag
      (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 6 xs) h6
    have hz7 := sameReject (leftOf ArgumentEntriesLayer.raw) (constant 2 7) tag (numeral 7) xs htag
      (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 7 xs) h7
    exact zeroBranchIntro _ _ _ z xs hz6
      (zeroBranchIntro _ _ _ z xs hz7
        (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xs))

theorem transportCase (six : Bool) (raw tag tail1 tail2 value : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (hn : Nonempty (Derivation body Delta (eqn tag (numeral 7)).not))
    (hc : Nonempty (Derivation body Delta (caseFormula six tag)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.step value raw tail1))) :
    Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.step value raw tail2)) := by
  have h1 := canonicalStep six raw tag tail1 ht hn hc
  have h2 := canonicalStep six raw tag tail2 ht hn hc
  have he := valueUnique ArgumentEntriesLayer.step (numeral (if six then 1 else 0)) value
    (Fin.cons raw (Fin.cons tail1 Fin.elim0)) h1 hv
  exact outputTransport ArgumentEntriesLayer.step (numeral (if six then 1 else 0)) value
    (Fin.cons raw (Fin.cons tail2 Fin.elim0)) he h2

theorem stepTransport : Targets.InternalStepTransport := by
  intro body alpha Delta raw tag tail1 tail2 value ht hn hv
  apply formulaCases (eqn tag (numeral 6))
  · exact transportCase true raw tag tail1 tail2 value
      (withHyp ht _) (withHyp hn _) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
  · exact transportCase false raw tag tail1 tail2 value
      (withHyp ht _) (withHyp hn _) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)

theorem canonicalLayer (six : Bool) (raw tag answers param : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (hn : Nonempty (Derivation body Delta (eqn tag (numeral 7)).not))
    (hc : Nonempty (Derivation body Delta (caseFormula six tag))) :
    Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.layer
      (suc (numeral (if six then 1 else 0))) raw answers param)) := by
  apply programCases InternalRawListRecursion.lookup (Fin.cons (numeral 1) (Fin.cons answers Fin.elim0)) _
  intro beta j Theta tailValue hj hl
  simp only [graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename]
  simp only [consTermRename,emptyRename,GuardedSourceSyntaxProof.numeralRename] at hl
  have htj := renameInto ht j Theta hj
  rw [graph1Rename] at htj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn tag (numeral 7)).relabel j).not) at hnj
  simp only [eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hcj := renameInto hc j Theta hj
  rw [caseRename] at hcj
  exact ArgumentEntriesTailCoherence.SupportProof.layerAtTail (raw.relabel j) (answers.relabel j) (param.relabel j)
    tailValue (numeral (if six then 1 else 0)) hl
    (canonicalStep six (raw.relabel j) (tag.relabel j) tailValue htj hnj hcj)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNonConsCoherence.StepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNonConsCoherence.StepProof
