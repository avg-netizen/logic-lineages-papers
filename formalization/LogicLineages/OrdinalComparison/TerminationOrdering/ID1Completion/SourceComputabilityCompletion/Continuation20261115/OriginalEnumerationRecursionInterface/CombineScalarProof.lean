module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.SelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.CombineScalarProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem answerAt (i : Nat) (node answers param value : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value (numeral i) answers))) :
    Nonempty (Derivation body Delta (graph3 (answer i) value node answers param)) :=
  binaryValue InternalRawListRecursion.lookup (OriginalRawSyntaxTransport.constant 3 i) (.projection 1)
    value (numeral i) answers ![node,answers,param] h
    (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue i ![node,answers,param])
    (projectionValue 1 ![node,answers,param])

theorem answerRecover (i : Nat) (node answers param value : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph3 (answer i) value node answers param))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value (numeral i) answers)) :=
  binaryRecover InternalRawListRecursion.lookup (OriginalRawSyntaxTransport.constant 3 i) (.projection 1)
    value (numeral i) answers ![node,answers,param] h
    (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue i ![node,answers,param])
    (projectionValue 1 ![node,answers,param])

theorem layerAt (n : Nat) (node answers param vb f ts hs ls tb p2 p3 prior opened value : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node vb f)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ts p2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p2 hs p3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3 ls tb)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup prior z answers)))
    (hb : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup opened (numeral 1) answers)))
    (hv : Nonempty (Derivation body Delta (programGraph (OriginalEnumerationConstructorLayer.layer n)
      value ![ts,hs,ls,tb,vb,prior,opened]))) :
    Nonempty (Derivation body Delta (graph3 (positiveLayer n) value node answers param)) := by
  apply compositionValue (OriginalEnumerationConstructorLayer.layer n)
    ![types,heads,labels,tupleBound,variableBound,answer 0,answer 1]
    value ![node,answers,param] ![ts,hs,ls,tb,vb,prior,opened] hv
  intro i
  fin_cases i
  · exact SelectorProof.typesAt node answers param ts p2 hp
  · exact SelectorProof.headsAt node answers param ts hs p2 p3 hp h2
  · exact SelectorProof.labelsAt node answers param ts hs ls tb p2 p3 hp h2 h3
  · exact SelectorProof.tupleBoundAt node answers param ts hs ls tb p2 p3 hp h2 h3
  · exact SelectorProof.variableBoundAt node answers param vb f hn
  · exact answerAt 0 node answers param prior ha
  · exact answerAt 1 node answers param opened hb

theorem layerRecover (n : Nat) (node answers param vb f ts hs ls tb p2 p3 prior opened value : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node vb f)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ts p2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p2 hs p3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3 ls tb)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup prior z answers)))
    (hb : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup opened (numeral 1) answers)))
    (hv : Nonempty (Derivation body Delta (graph3 (positiveLayer n) value node answers param))) :
    Nonempty (Derivation body Delta (programGraph (OriginalEnumerationConstructorLayer.layer n)
      value ![ts,hs,ls,tb,vb,prior,opened])) := by
  apply compositionRecover (OriginalEnumerationConstructorLayer.layer n)
    ![types,heads,labels,tupleBound,variableBound,answer 0,answer 1]
    value ![node,answers,param] ![ts,hs,ls,tb,vb,prior,opened] hv
  intro i
  fin_cases i
  · exact SelectorProof.typesAt node answers param ts p2 hp
  · exact SelectorProof.headsAt node answers param ts hs p2 p3 hp h2
  · exact SelectorProof.labelsAt node answers param ts hs ls tb p2 p3 hp h2 h3
  · exact SelectorProof.tupleBoundAt node answers param ts hs ls tb p2 p3 hp h2 h3
  · exact SelectorProof.variableBoundAt node answers param vb f hn
  · exact answerAt 0 node answers param prior ha
  · exact answerAt 1 node answers param opened hb

theorem zeroValue (n : Nat) (node answers param : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph3 fuel z node answers param))) :
    Nonempty (Derivation body Delta (graph3 (G n) (numeral 1) node answers param)) :=
  unaryValue .succ (InternalAcceptance.branch fuel (InternalAcceptance.constantZero 3) (positiveLayer n))
    (suc z) z ![node,answers,param] (successorValue (Fin.cons z Fin.elim0))
    (zeroBranchIntro fuel (InternalAcceptance.constantZero 3) (positiveLayer n) z ![node,answers,param]
      hf (InternalAcceptanceConjunctionProof.constantZeroValue ![node,answers,param]))

theorem positiveValue (n : Nat) (node answers param k value : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph3 fuel (suc k) node answers param)))
    (hv : Nonempty (Derivation body Delta (graph3 (positiveLayer n) value node answers param))) :
    Nonempty (Derivation body Delta (graph3 (G n) (suc value) node answers param)) :=
  unaryValue .succ (InternalAcceptance.branch fuel (InternalAcceptance.constantZero 3) (positiveLayer n))
    (suc value) value ![node,answers,param] (successorValue (Fin.cons value Fin.elim0))
    (successorBranchIntro fuel (InternalAcceptance.constantZero 3) (positiveLayer n) value k
      ![node,answers,param] hf hv)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.CombineScalarProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.CombineScalarProof
