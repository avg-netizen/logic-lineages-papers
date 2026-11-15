module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.SelectorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rankAt (node param vb f : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node vb f))) :
    Nonempty (Derivation body Delta (graph2 R f node param)) :=
  unaryValue InternalUnpair.right (.projection 0) f node ![node,param]
    (pairRight node vb f hp) (projectionValue 0 ![node,param])

theorem previousAt (node param f : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 R (suc f) node param))) :
    Nonempty (Derivation body Delta (graph2 previousFuel f node param)) :=
  unaryValue InternalEqualityTest.predecessor R f (suc f) ![node,param]
    (InternalEqualityTestPredecessorProof.predecessorSuccessor f) hr

theorem boundAt (node param vb f : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node vb f))) :
    Nonempty (Derivation body Delta (graph2 bound vb node param)) :=
  unaryValue InternalUnpair.left (.projection 0) vb node ![node,param]
    (pairLeft node vb f hp) (projectionValue 0 ![node,param])

theorem fuelAt (node answers param vb f : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node vb f))) :
    Nonempty (Derivation body Delta (graph3 fuel f node answers param)) :=
  unaryValue InternalUnpair.right (.projection 0) f node ![node,answers,param]
    (pairRight node vb f hp) (projectionValue 0 ![node,answers,param])

theorem variableBoundAt (node answers param vb f : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node vb f))) :
    Nonempty (Derivation body Delta (graph3 variableBound vb node answers param)) :=
  unaryValue InternalUnpair.left (.projection 0) vb node ![node,answers,param]
    (pairLeft node vb f hp) (projectionValue 0 ![node,answers,param])

theorem typesAt (node answers param ts p2 : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ts p2))) :
    Nonempty (Derivation body Delta (graph3 types ts node answers param)) :=
  unaryValue InternalUnpair.left (.projection 2) ts param ![node,answers,param]
    (pairLeft param ts p2 hp) (projectionValue 2 ![node,answers,param])

theorem parameterTailAt (node answers param ts p2 : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ts p2))) :
    Nonempty (Derivation body Delta (graph3 (rightOf (.projection 2)) p2 node answers param)) :=
  unaryValue InternalUnpair.right (.projection 2) p2 param ![node,answers,param]
    (pairRight param ts p2 hp) (projectionValue 2 ![node,answers,param])

theorem headsAt (node answers param ts hs p2 p3 : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ts p2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p2 hs p3))) :
    Nonempty (Derivation body Delta (graph3 heads hs node answers param)) :=
  unaryValue InternalUnpair.left (rightOf (.projection 2)) hs p2 ![node,answers,param]
    (pairLeft p2 hs p3 h2) (parameterTailAt node answers param ts p2 hp)

theorem parameterTailTailAt (node answers param ts hs p2 p3 : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ts p2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p2 hs p3))) :
    Nonempty (Derivation body Delta (graph3 (rightOf (rightOf (.projection 2))) p3 node answers param)) :=
  unaryValue InternalUnpair.right (rightOf (.projection 2)) p3 p2 ![node,answers,param]
    (pairRight p2 hs p3 h2) (parameterTailAt node answers param ts p2 hp)

theorem labelsAt (node answers param ts hs ls tb p2 p3 : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ts p2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p2 hs p3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3 ls tb))) :
    Nonempty (Derivation body Delta (graph3 labels ls node answers param)) :=
  unaryValue InternalUnpair.left (rightOf (rightOf (.projection 2))) ls p3 ![node,answers,param]
    (pairLeft p3 ls tb h3) (parameterTailTailAt node answers param ts hs p2 p3 hp h2)

theorem tupleBoundAt (node answers param ts hs ls tb p2 p3 : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ts p2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p2 hs p3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3 ls tb))) :
    Nonempty (Derivation body Delta (graph3 tupleBound tb node answers param)) :=
  unaryValue InternalUnpair.right (rightOf (rightOf (.projection 2))) tb p3 ![node,answers,param]
    (pairRight p3 ls tb h3) (parameterTailTailAt node answers param ts hs p2 p3 hp h2)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.SelectorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.SelectorProof
