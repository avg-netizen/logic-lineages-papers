module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.AnswerPairProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.ValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open OriginalEnumerationRecursionInterface
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atValues (n : Nat) (node param vb f ts hs ls tb p2 p3 a c prior opened deps tail values rest out : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node vb (suc f))))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ts p2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p2 hs p3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3 ls tb)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing a vb f)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing c (suc vb) f)))
    (hea : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) prior a param)))
    (hec : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) opened c param)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tail c z)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps a tail)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest opened z)))
    (hv : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values prior rest)))
    (hl : Nonempty (Derivation body Delta (programGraph (OriginalEnumerationConstructorLayer.layer n)
      out ![ts,hs,ls,tb,vb,prior,opened]))) :
    Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out node param)) := by
  have hdeps := AnswerPairProof.dependencies node param vb f a c deps tail hn ha hc ht hd
  have hmap := AnswerPairProof.mapPair n a c prior opened deps tail values rest param hea hec ht hd hr hv
  have hans : Nonempty (Derivation body Delta
      (graph2 (OriginalEnumerationEquation.answers n) values node param)) :=
    binaryValue (OriginalEnumerationEquation.answerMap n) D (.projection 1)
      values deps param ![node,param] hmap hdeps (projectionValue 1 ![node,param])
  have hla := AnswerPairProof.firstLookup values prior rest hv
  have hlc := AnswerPairProof.secondLookup values prior rest opened hv hr
  have hpos := CombineScalarProof.layerAt n node values param vb (suc f) ts hs ls tb p2 p3 prior opened out
    hn hp h2 h3 hla hlc hl
  have hg := CombineScalarProof.positiveValue n node values param f out
    (SelectorProof.fuelAt node values param vb (suc f) hn) hpos
  exact (OriginalEnumerationEquation.StatementChecks.exactEnumerationEquation n body alpha Delta
    node param values out hans).mpr hg
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.ValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.ValueProof
