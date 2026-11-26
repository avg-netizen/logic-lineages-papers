module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem leftGraph (base target out : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract out base (numeral 0)))) :
    Nonempty (Derivation body Delta (graph2 leftEntries out base target)) :=
  binaryValue ArgumentEntriesRecursor.extract (.projection 0) (constant 2 0) out base (numeral 0)
    ![base,target] h (projectionValue 0 ![base,target]) (constantValue 0 ![base,target])

theorem rightGraph (base target out : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract out target (numeral 0)))) :
    Nonempty (Derivation body Delta (graph2 rightEntries out base target)) :=
  binaryValue ArgumentEntriesRecursor.extract (.projection 1) (constant 2 0) out target (numeral 0)
    ![base,target] h (projectionValue 1 ![base,target]) (constantValue 0 ![base,target])

theorem internalNone : Targets.InternalNone := by
  intro body alpha Delta base target
  constructor
  · intro hs
    exact zeroBranchIntro leftEntries (constant 2 0)
      (InternalAcceptance.branch rightEntries (constant 2 0) compare) (numeral 0) ![base,target]
      (leftGraph base target (numeral 0) hs) (constantValue 0 ![base,target])
  · intro sourceList hs ht
    have hinner := zeroBranchIntro rightEntries (constant 2 0) compare (numeral 0) ![base,target]
      (rightGraph base target (numeral 0) ht) (constantValue 0 ![base,target])
    exact successorBranchIntro leftEntries (constant 2 0)
      (InternalAcceptance.branch rightEntries (constant 2 0) compare) (numeral 0) sourceList ![base,target]
      (leftGraph base target (suc sourceList) hs) hinner

theorem internalSome : Targets.InternalSome := by
  intro body alpha Delta base target sourceList targetList out hs ht
  let xs : Fin 2 → OTerm alpha := ![base,target]
  have hl := leftGraph base target (suc sourceList) hs
  have hr := rightGraph base target (suc targetList) ht
  have hpl : Nonempty (Derivation body Delta (programGraph leftList sourceList xs)) :=
    unaryValue InternalEqualityTest.predecessor leftEntries sourceList (suc sourceList) xs
      (InternalEqualityTestPredecessorProof.predecessorSuccessor sourceList) hl
  have hpr : Nonempty (Derivation body Delta (programGraph rightList targetList xs)) :=
    unaryValue InternalEqualityTest.predecessor rightEntries targetList (suc targetList) xs
      (InternalEqualityTestPredecessorProof.predecessorSuccessor targetList) hr
  constructor
  · intro h
    have hi := successorBranchElim leftEntries (constant 2 0)
      (InternalAcceptance.branch rightEntries (constant 2 0) compare) out sourceList xs hl h
    have hc := successorBranchElim rightEntries (constant 2 0) compare out targetList xs hr hi
    exact binaryRecover ArgumentCountComparison.permutation leftList rightList out sourceList targetList xs hc hpl hpr
  · intro h
    have hc := binaryValue ArgumentCountComparison.permutation leftList rightList out sourceList targetList xs h hpl hpr
    have hi := successorBranchIntro rightEntries (constant 2 0) compare out targetList xs hr hc
    exact successorBranchIntro leftEntries (constant 2 0)
      (InternalAcceptance.branch rightEntries (constant 2 0) compare) out sourceList xs hl hi

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.InternalProof
