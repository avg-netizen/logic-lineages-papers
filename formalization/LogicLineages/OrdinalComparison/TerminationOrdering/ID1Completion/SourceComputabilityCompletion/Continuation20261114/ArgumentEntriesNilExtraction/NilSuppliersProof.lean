module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.NilSuppliersProof
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

open InternalApplicationCertificateConstructorsSupportProof
open InternalAcceptanceBranchProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem childrenNil (raw : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0))) :
    Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children z raw)) := by
  apply zeroBranchIntro _ _ _ z (Fin.cons raw Fin.elim0)
  · exact nilArity (.projection 0) raw (Fin.cons raw Fin.elim0)
      (projectionValue 0 (Fin.cons raw Fin.elim0)) hc
  · exact constantValue 0 (Fin.cons raw Fin.elim0)

theorem stepNil (raw tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0))) :
    Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.step (numeral 1) raw tail)) := by
  apply branchNumeralIntro 6 6 (leftOf ArgumentEntriesLayer.raw) _ _ (numeral 1) (Fin.cons raw (Fin.cons tail Fin.elim0))
  · exact OriginalRawSyntaxTransportInternalConstructorFieldsProof.nilTag (.projection 0) raw
      (Fin.cons raw (Fin.cons tail Fin.elim0)) (projectionValue 0 (Fin.cons raw (Fin.cons tail Fin.elim0))) hc
  · exact constantValue 1 (Fin.cons raw (Fin.cons tail Fin.elim0))

theorem recombineNil (raw answers : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0))) :
    Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.recombine (numeral 2) raw answers)) := by
  apply programCases ArgumentEntriesLayer.tailAnswer (Fin.cons raw (Fin.cons answers Fin.elim0)) _
  intro beta j Theta tail hj ht
  simp only [consTermRename,emptyRename] at ht
  have hcj := renameInto hc j Theta hj
  simp only [programRename,emptyRename] at hcj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  let xs : Fin 2 → OTerm beta := Fin.cons (raw.relabel j) (Fin.cons (answers.relabel j) Fin.elim0)
  have hs := binaryValue ArgumentEntriesLayer.step (.projection 0) ArgumentEntriesLayer.tailAnswer
    (numeral 1) (raw.relabel j) tail xs (stepNil (raw.relabel j) tail hcj) (projectionValue 0 xs) ht
  exact unaryValue .succ (.composition ArgumentEntriesLayer.step ![.projection 0,ArgumentEntriesLayer.tailAnswer])
    (numeral 2) (numeral 1) xs (successorValue (Fin.cons (numeral 1) Fin.elim0)) hs

theorem nilSuppliers : Targets.InternalNilSuppliers := by
  intro body alpha Delta raw answers param hc
  apply andIntro
  · exact unaryValue ArgumentEntriesChildren.children (.projection 0) z raw
      (Fin.cons raw (Fin.cons param Fin.elim0)) (childrenNil raw hc)
      (projectionValue 0 (Fin.cons raw (Fin.cons param Fin.elim0)))
  · exact binaryValue ArgumentEntriesLayer.recombine (.projection 0) (.projection 1) (numeral 2) raw answers
      (Fin.cons raw (Fin.cons answers (Fin.cons param Fin.elim0))) (recombineNil raw answers hc)
      (projectionValue 0 (Fin.cons raw (Fin.cons answers (Fin.cons param Fin.elim0))))
      (projectionValue 1 (Fin.cons raw (Fin.cons answers (Fin.cons param Fin.elim0))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.NilSuppliersProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.NilSuppliersProof
