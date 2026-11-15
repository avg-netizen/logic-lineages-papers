module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.MapProof
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
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ExchangeMapGraph

theorem presentStep (key entries value rest out : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 lookup (suc value) entries key)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out value rest))) :
    Nonempty (Derivation body Delta (programGraph mapStep out ![key,rest,entries])) := by
  let xs : Fin 3 → OTerm alpha := ![key,rest,entries]
  have hf := binaryValue lookup (.projection 2) (.projection 0) (suc value) entries key xs hl
    (projectionValue 2 xs) (projectionValue 0 xs)
  have hp := unaryValue InternalEqualityTest.predecessor found value (suc value) xs
    (InternalEqualityTestPredecessorProof.predecessorSuccessor value) hf
  exact successorBranchIntro found (.projection 1) _ out value xs hf
    (binaryValue InternalListCodec.consCode (.composition InternalEqualityTest.predecessor (fun _ : Fin 1 => found))
      (.projection 1) out value rest xs hc hp (projectionValue 1 xs))

theorem present : Targets.InternalMapPresent := by
  intro body alpha Delta keys key tail entries value rest out hk hl hr hc
  exact InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 1) mapStep
    keys key tail rest out (Fin.cons entries Fin.elim0) hk hr (presentStep key entries value rest out hl hc)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.MapProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.MapProof
