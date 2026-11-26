module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.StepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceBranchProof InternalAcceptanceNormalizationProof
open InternalTagArithmeticSyntaxProof (eqn suc)
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem queryEqual (head acc needle : OTerm alpha)
    (h : Nonempty (Derivation body Delta (eqn head needle))) :
    Nonempty (Derivation body Delta (programGraph (sameOf (.projection 0) (.projection 2))
      (numeral 1) ![head,acc,needle])) :=
  binaryValue InternalEqualityTest.equalityTest (.projection 0) (.projection 2) (numeral 1)
    head needle ![head,acc,needle] (InternalEqualityTestCompositionProof.equalityOfEqual head needle h)
    (projectionValue 0 ![head,acc,needle]) (projectionValue 2 ![head,acc,needle])

theorem queryUnequal (head acc needle : OTerm alpha)
    (h : Nonempty (Derivation body Delta (eqn head needle).not)) :
    Nonempty (Derivation body Delta (programGraph (sameOf (.projection 0) (.projection 2))
      (numeral 0) ![head,acc,needle])) := by
  apply OriginalRawSyntaxTransportInternalConstructorSupportProof.sameReject
    (.projection 0) (.projection 2) head needle ![head,acc,needle]
    (projectionValue 0 ![head,acc,needle]) (projectionValue 2 ![head,acc,needle])
  simpa only [equalEqn] using h

theorem equalStep (head acc needle : OTerm alpha)
    (h : Nonempty (Derivation body Delta (eqn head needle))) :
    Nonempty (Derivation body Delta (graph3 step (suc acc) head acc needle)) := by
  let xs : Fin 3 → OTerm alpha := ![head,acc,needle]
  let query : Program 3 := sameOf (.projection 0) (.projection 2)
  have hs : Nonempty (Derivation body Delta (programGraph (succOf (.projection 1)) (suc acc) xs)) :=
    unaryValue .succ (.projection 1) (suc acc) acc xs
      (InternalControlGraphSupportProof.successorValue (Fin.cons acc Fin.elim0)) (projectionValue 1 xs)
  exact successorBranchIntro query (.projection 1) (succOf (.projection 1))
    (suc acc) (numeral 0) xs (queryEqual head acc needle h) hs

theorem unequalStep (head acc needle : OTerm alpha)
    (h : Nonempty (Derivation body Delta (eqn head needle).not)) :
    Nonempty (Derivation body Delta (graph3 step acc head acc needle)) := by
  let xs : Fin 3 → OTerm alpha := ![head,acc,needle]
  let query : Program 3 := sameOf (.projection 0) (.projection 2)
  exact zeroBranchIntro query (.projection 1) (succOf (.projection 1))
    acc xs (queryUnequal head acc needle h) (projectionValue 1 xs)

theorem internalNil : Targets.InternalNil := by
  intro body alpha Delta needle
  exact InternalRawListRecursionProof.nilValue (constant 1 0) step (numeral 0)
    (Fin.cons needle Fin.elim0)
    (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 (Fin.cons needle Fin.elim0))

theorem internalEqualCons : Targets.InternalEqualCons := by
  intro body alpha Delta list head tail needle acc hc hr he
  exact InternalRawListRecursionProof.consValue (constant 1 0) step list head tail acc (suc acc)
    (Fin.cons needle Fin.elim0) hc hr (equalStep head acc needle he)

theorem internalUnequalCons : Targets.InternalUnequalCons := by
  intro body alpha Delta list head tail needle acc hc hr he
  exact InternalRawListRecursionProof.consValue (constant 1 0) step list head tail acc acc
    (Fin.cons needle Fin.elim0) hc hr (unequalStep head acc needle he)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
