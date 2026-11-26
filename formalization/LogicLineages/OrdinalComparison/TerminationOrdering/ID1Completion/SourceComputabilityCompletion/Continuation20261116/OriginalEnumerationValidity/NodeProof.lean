module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.AnswersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.NodeProof
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
theorem dependencies (node param bound fuel prior opened rest deps : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node bound (suc fuel))))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing prior bound fuel)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing opened (suc bound) fuel)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest opened z)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps prior rest))) :
    Nonempty (Derivation body Delta (graph2 D deps node param)) := by
  let xs : Fin 2 → OTerm alpha := ![node,param]
  have hr := SelectorProof.rankAt node param bound (suc fuel) hn
  have hb := SelectorProof.boundAt node param bound (suc fuel) hn
  have hf := SelectorProof.previousAt node param fuel hr
  have hprior := binaryValue InternalPairing.pairing OriginalEnumerationRecursionInterface.bound previousFuel
    prior bound fuel xs hp hb hf
  have hsb := unaryValue .succ OriginalEnumerationRecursionInterface.bound (suc bound) bound xs
    (successorValue ![bound]) hb
  have hopened := binaryValue InternalPairing.pairing
    (.composition .succ (fun _ : Fin 1 => OriginalEnumerationRecursionInterface.bound)) previousFuel
    opened (suc bound) fuel xs ho hsb hf
  have hrest := binaryValue InternalListCodec.consCode openedNode (InternalAcceptance.constantZero 2)
    rest opened z xs ht hopened (InternalAcceptanceConjunctionProof.constantZeroValue xs)
  have hdeps := binaryValue InternalListCodec.consCode priorNode
    (.composition InternalListCodec.consCode ![openedNode,InternalAcceptance.constantZero 2])
    deps prior rest xs hd hprior hrest
  exact successorBranchIntro R (InternalAcceptance.constantZero 2) positiveDependencies deps fuel xs hr hdeps

theorem childValid (n : Nat) (fuel bound node param out : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRank n (suc fuel))))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node bound fuel)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out node param))) :
    Nonempty (Derivation body Delta (Lists.AllValid n out)) :=
  InductionBindingProof.atRankApply n fuel node param out
    (InductionBindingProof.belowRankAt n (suc fuel) fuel ih
      (InternalCoprimeMultipleBoundedProof.selfLtSucc fuel))
    (andIntro (SelectorProof.rankAt node param bound fuel hn) he)

theorem orderedAnswers (n : Nat) (node param bound fuel prior opened rest deps a b tail answers : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node bound (suc fuel))))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing prior bound fuel)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing opened (suc bound) fuel)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest opened z)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps prior rest)))
    (ha : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) a prior param)))
    (hb : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) b opened param)))
    (hbt : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tail b z)))
    (hat : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode answers a tail))) :
    Nonempty (Derivation body Delta (graph2 (OriginalEnumerationEquation.answers n) answers node param)) :=
  AnswersProof.answersAt n node param deps answers (dependencies node param bound fuel prior opened rest deps hn hp ho ht hd)
    (AnswersProof.consMap n deps prior rest tail param a answers hd
      (AnswersProof.consMap n rest opened z z param b tail ht (AnswersProof.nilMap n param) hb hbt) ha hat)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.NodeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.NodeProof
