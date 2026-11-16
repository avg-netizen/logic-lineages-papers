module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.AnswersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.WitnessProof
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
def restNodes : Program 2 := .composition InternalListCodec.consCode ![openedNode,constant 2 0]
def depsNodes : Program 2 := .composition InternalListCodec.consCode ![priorNode,restNodes]
def firstValue (n : Nat) : Program 2 := .composition (OriginalEnumerationRecursion.enumeration n) ![priorNode,.projection 1]
def secondValue (n : Nat) : Program 2 := .composition (OriginalEnumerationRecursion.enumeration n) ![openedNode,.projection 1]
def restValues (n : Nat) : Program 2 := .composition InternalListCodec.consCode ![secondValue n,constant 2 0]
def allValues (n : Nat) : Program 2 := .composition InternalListCodec.consCode ![firstValue n,restValues n]
def queries (n : Nat) : Fin 8 → Program 2 :=
  ![priorNode,openedNode,restNodes,depsNodes,firstValue n,secondValue n,restValues n,allValues n]

theorem cases (n : Nat) (node param bound fuel : OTerm alpha) (C : Formula alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node bound (suc fuel))))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (ys : Fin 8 → OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (ys 0) (bound.relabel j) (fuel.relabel j))) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (ys 1) (suc (bound.relabel j)) (fuel.relabel j))) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode (ys 2) (ys 1) z)) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode (ys 3) (ys 0) (ys 2))) →
      Nonempty (Derivation body Theta (graph2 (OriginalEnumerationRecursion.enumeration n) (ys 4) (ys 0) (param.relabel j))) →
      Nonempty (Derivation body Theta (graph2 (OriginalEnumerationRecursion.enumeration n) (ys 5) (ys 1) (param.relabel j))) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode (ys 6) (ys 5) z)) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode (ys 7) (ys 4) (ys 6))) →
      Nonempty (Derivation body Theta (C.relabel j))) : Nonempty (Derivation body Delta C) := by
  apply queryCases (queries n) (Fin.cons node (Fin.cons param Fin.elim0)) C
  intro beta j ys Theta hj hq
  simp only [consTermRename,emptyRename] at hq
  have hnj := renameInto hn j Theta hj
  simp only [graph2Rename,InternalTagArithmeticSyntaxProof.sucRelabel] at hnj
  let xs : Fin 2 → OTerm beta := ![node.relabel j,param.relabel j]
  have hr := SelectorProof.rankAt (node.relabel j) (param.relabel j) (bound.relabel j) (suc (fuel.relabel j)) hnj
  have hb := SelectorProof.boundAt (node.relabel j) (param.relabel j) (bound.relabel j) (suc (fuel.relabel j)) hnj
  have hf := SelectorProof.previousAt (node.relabel j) (param.relabel j) (fuel.relabel j) hr
  have hsb := unaryValue .succ OriginalEnumerationRecursionInterface.bound (suc (bound.relabel j)) (bound.relabel j) xs
    (successorValue ![bound.relabel j]) hb
  have hprior := binaryRecover InternalPairing.pairing OriginalEnumerationRecursionInterface.bound previousFuel
    (ys 0) (bound.relabel j) (fuel.relabel j) xs (hq 0) hb hf
  have hopened := binaryRecover InternalPairing.pairing
    (.composition .succ (fun _ : Fin 1 => OriginalEnumerationRecursionInterface.bound)) previousFuel
    (ys 1) (suc (bound.relabel j)) (fuel.relabel j) xs (hq 1) hsb hf
  have ht := binaryRecover InternalListCodec.consCode openedNode (constant 2 0)
    (ys 2) (ys 1) z xs (hq 2) (hq 1) (constantValue 0 xs)
  have hd := binaryRecover InternalListCodec.consCode priorNode restNodes
    (ys 3) (ys 0) (ys 2) xs (hq 3) (hq 0) (hq 2)
  have ha := binaryRecover (OriginalEnumerationRecursion.enumeration n) priorNode (.projection 1)
    (ys 4) (ys 0) (param.relabel j) xs (hq 4) (hq 0) (projectionValue 1 xs)
  have hbb := binaryRecover (OriginalEnumerationRecursion.enumeration n) openedNode (.projection 1)
    (ys 5) (ys 1) (param.relabel j) xs (hq 5) (hq 1) (projectionValue 1 xs)
  have hvt := binaryRecover InternalListCodec.consCode (secondValue n) (constant 2 0)
    (ys 6) (ys 5) z xs (hq 6) (hq 5) (constantValue 0 xs)
  have hva := binaryRecover InternalListCodec.consCode (firstValue n) (restValues n)
    (ys 7) (ys 4) (ys 6) xs (hq 7) (hq 4) (hq 6)
  exact next beta j Theta ys hj hprior hopened ht hd ha hbb hvt hva
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.WitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.WitnessProof
