module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.ZeroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.DependencyPositiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.AnswerPairProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open OriginalEnumerationRecursionInterface
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem step (n : Nat) (child previous param value out : OTerm alpha)
    (he : Nonempty (Derivation body Delta
      (graph2 (OriginalEnumerationRecursion.enumeration n) value child param)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out value previous))) :
    Nonempty (Derivation body Delta
      (graph3 (OriginalEnumerationEquation.answerStep n) out child previous param)) := by
  apply binaryValue InternalListCodec.consCode
    (.composition (OriginalEnumerationRecursion.enumeration n) ![.projection 0,.projection 2])
    (.projection 1) out value previous ![child,previous,param] hc
  · exact binaryValue (OriginalEnumerationRecursion.enumeration n) (.projection 0) (.projection 2)
      value child param ![child,previous,param] he
      (projectionValue 0 ![child,previous,param]) (projectionValue 2 ![child,previous,param])
  · exact projectionValue 1 ![child,previous,param]

theorem mapPair (n : Nat) (a c prior opened deps tail values rest param : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) prior a param)))
    (hc : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) opened c param)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tail c z)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps a tail)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest opened z)))
    (hv : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values prior rest))) :
    Nonempty (Derivation body Delta (graph2 (OriginalEnumerationEquation.answerMap n) values deps param)) := by
  have hz := InternalRawListRecursionProof.nilValue (body := body) (Gamma := Delta) (InternalAcceptance.constantZero 1)
    (OriginalEnumerationEquation.answerStep n) z (Fin.cons param Fin.elim0)
    (InternalAcceptanceConjunctionProof.constantZeroValue (Fin.cons param Fin.elim0))
  have htail := InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 1)
    (OriginalEnumerationEquation.answerStep n) tail c z z rest (Fin.cons param Fin.elim0)
    ht hz (step n c z param opened rest hc hr)
  exact InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 1)
    (OriginalEnumerationEquation.answerStep n) deps a tail rest values (Fin.cons param Fin.elim0)
    hd htail (step n a rest param prior values ha hv)

theorem dependencies (node param vb f a c deps tail : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node vb (suc f))))
    (ha : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing a vb f)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing c (suc vb) f)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tail c z)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps a tail))) :
    Nonempty (Derivation body Delta (graph2 D deps node param)) := by
  have hr := SelectorProof.rankAt node param vb (suc f) hn
  have hp := SelectorProof.previousAt node param f hr
  have hb := SelectorProof.boundAt node param vb (suc f) hn
  have hprior : Nonempty (Derivation body Delta (graph2 priorNode a node param)) :=
    binaryValue InternalPairing.pairing bound previousFuel a vb f ![node,param] ha hb hp
  have hsb : Nonempty (Derivation body Delta
      (graph2 (.composition .succ (fun _ : Fin 1 => bound)) (suc vb) node param)) :=
    unaryValue .succ bound (suc vb) vb ![node,param]
      (successorValue (Fin.cons vb Fin.elim0)) hb
  have hopened : Nonempty (Derivation body Delta (graph2 openedNode c node param)) :=
    binaryValue InternalPairing.pairing (.composition .succ (fun _ : Fin 1 => bound))
      previousFuel c (suc vb) f ![node,param] hc hsb hp
  have htail : Nonempty (Derivation body Delta
      (graph2 DependencyPositiveProof.tailProgram tail node param)) :=
    binaryValue InternalListCodec.consCode openedNode (InternalAcceptance.constantZero 2)
      tail c z ![node,param] ht hopened
      (InternalAcceptanceConjunctionProof.constantZeroValue ![node,param])
  have hdeps : Nonempty (Derivation body Delta (graph2 positiveDependencies deps node param)) :=
    binaryValue InternalListCodec.consCode priorNode DependencyPositiveProof.tailProgram
      deps a tail ![node,param] hd hprior htail
  exact InternalAcceptanceBranchProof.successorBranchIntro R (InternalAcceptance.constantZero 2)
    positiveDependencies deps f ![node,param] hr hdeps

theorem firstLookup (values prior rest : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values prior rest))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup prior z values)) :=
  InternalRawListRecursionSupportProof.lookupValue prior z values values
    (InternalRawListRecursionSupportProof.dropZero values)
    (InternalRawListRecursionSupportProof.consHead values prior rest hv)

theorem secondLookup (values prior rest opened : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values prior rest)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest opened z))) :
    Nonempty (Derivation body Delta
      (graph2 InternalRawListRecursion.lookup opened (suc z) values)) :=
  InternalRawListRecursionSupportProof.lookupValue opened (suc z) values rest
    (InternalRawListRecursionSupportProof.dropNext rest values z values
      (InternalRawListRecursionSupportProof.dropZero values)
      (InternalRawListRecursionSupportProof.consTail values prior rest hv))
    (InternalRawListRecursionSupportProof.consHead rest opened z hr)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.AnswerPairProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.AnswerPairProof
