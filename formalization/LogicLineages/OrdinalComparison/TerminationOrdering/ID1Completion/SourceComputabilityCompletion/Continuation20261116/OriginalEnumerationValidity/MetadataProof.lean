module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.AnswersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.MetadataProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open OriginalEnumerationRecursionInterface
open InternalAcceptanceBranchProof
open InternalApplicationStepPeelSupportProof (andIntro)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
def tailParam : Program 2 := rightOf (.projection 1)
def innerParam : Program 2 := rightOf tailParam
def queries : Fin 7 → Program 2 :=
  ![OriginalEnumerationRecursionInterface.bound,leftOf (.projection 1),tailParam,
    leftOf tailParam,innerParam,leftOf innerParam,rightOf innerParam]

theorem cases (node param fuel : OTerm alpha) (C : Formula alpha)
    (hr : Nonempty (Derivation body Delta (graph2 R fuel node param)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (ys : Fin 7 → OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (node.relabel j) (ys 0) (fuel.relabel j))) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (param.relabel j) (ys 1) (ys 2))) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (ys 2) (ys 3) (ys 4))) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (ys 4) (ys 5) (ys 6))) →
      Nonempty (Derivation body Theta (C.relabel j))) : Nonempty (Derivation body Delta C) := by
  apply queryCases queries (Fin.cons node (Fin.cons param Fin.elim0)) C
  intro beta j ys Theta hj hq
  simp only [consTermRename,emptyRename] at hq
  have hrj := renameInto hr j Theta hj
  rw [graph2Rename] at hrj
  let xs : Fin 2 → OTerm beta := ![node.relabel j,param.relabel j]
  have hn0 := unaryRecover InternalUnpair.left (.projection 0) (ys 0) (node.relabel j) xs (hq 0) (projectionValue 0 xs)
  have hn1 := unaryRecover InternalUnpair.right (.projection 0) (fuel.relabel j) (node.relabel j) xs hrj (projectionValue 0 xs)
  have hp0 := unaryRecover InternalUnpair.left (.projection 1) (ys 1) (param.relabel j) xs (hq 1) (projectionValue 1 xs)
  have hp1 := unaryRecover InternalUnpair.right (.projection 1) (ys 2) (param.relabel j) xs (hq 2) (projectionValue 1 xs)
  have h20 := unaryRecover InternalUnpair.left tailParam (ys 3) (ys 2) xs (hq 3) (hq 2)
  have h21 := unaryRecover InternalUnpair.right tailParam (ys 4) (ys 2) xs (hq 4) (hq 2)
  have h30 := unaryRecover InternalUnpair.left innerParam (ys 5) (ys 4) xs (hq 5) (hq 4)
  have h31 := unaryRecover InternalUnpair.right innerParam (ys 6) (ys 4) xs (hq 6) (hq 4)
  exact next beta j Theta ys hj
    (reconstructPair (node.relabel j) (ys 0) (fuel.relabel j) hn0 hn1)
    (reconstructPair (param.relabel j) (ys 1) (ys 2) hp0 hp1)
    (reconstructPair (ys 2) (ys 3) (ys 4) h20 h21)
    (reconstructPair (ys 4) (ys 5) (ys 6) h30 h31)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.MetadataProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.MetadataProof
