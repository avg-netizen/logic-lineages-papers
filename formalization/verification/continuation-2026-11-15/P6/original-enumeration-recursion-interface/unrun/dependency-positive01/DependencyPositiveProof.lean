module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.DependencySupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.DependencyPositiveProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSupportProof (refl)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def tailProgram : Program 2 := .composition InternalListCodec.consCode ![openedNode,InternalAcceptance.constantZero 2]

theorem observed (node param deps child childRank f vb a c tail : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 R (suc f) node param)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps node param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hcr : Nonempty (Derivation body Delta (graph2 R childRank child param)))
    (hb : Nonempty (Derivation body Delta (graph2 bound vb node param)))
    (ha : Nonempty (Derivation body Delta (graph2 priorNode a node param)))
    (hc : Nonempty (Derivation body Delta (graph2 openedNode c node param)))
    (ht : Nonempty (Derivation body Delta (graph2 tailProgram tail node param))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank (suc f))) := by
  have hf := SelectorProof.previousAt node param f hr
  have hpa := binaryRecover InternalPairing.pairing bound previousFuel a vb f ![node,param] ha hb hf
  have hsb : Nonempty (Derivation body Delta
      (graph2 (.composition .succ (fun _ : Fin 1 => bound)) (suc vb) node param)) :=
    unaryValue .succ bound (suc vb) vb ![node,param]
      (InternalControlGraphSupportProof.successorValue (Fin.cons vb Fin.elim0)) hb
  have hpc := binaryRecover InternalPairing.pairing (.composition .succ (fun _ : Fin 1 => bound))
    previousFuel c (suc vb) f ![node,param] hc hsb hf
  have htail := binaryRecover InternalListCodec.consCode openedNode (InternalAcceptance.constantZero 2)
    tail c z ![node,param] ht hc (InternalAcceptanceConjunctionProof.constantZeroValue ![node,param])
  have hpositive := successorBranchElim R (InternalAcceptance.constantZero 2) positiveDependencies
    deps f ![node,param] hr hd
  have hdeps := binaryRecover InternalListCodec.consCode priorNode tailProgram deps a tail ![node,param]
    hpositive ha ht
  have hchild := DependencySupportProof.memberRank param deps child a c tail f hdeps htail hm
    (SelectorProof.rankAt a param vb f hpa) (SelectorProof.rankAt c param (suc vb) f hpc)
  have he := valueUnique R childRank f ![child,param] hcr hchild
  exact InternalOriginalPairingOrderArithmeticProof.strictTransport childRank (suc f) f (suc f)
    he ⟨refl (suc f)⟩ ⟨InternalQuotientComparisonProof.equalToNext (refl f)⟩

theorem positive (node param deps child childRank f : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 R (suc f) node param)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps node param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hcr : Nonempty (Derivation body Delta (graph2 R childRank child param))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank (suc f))) := by
  let qs : Fin 4 → Program 2 := ![bound,priorNode,openedNode,tailProgram]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs ![node,param] _
  intro beta j ys Theta hj hq
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename] at hq
  simp only [InternalLessThan.strictLess,InternalOriginalOrderSyntaxProof.orderRename,sucRelabel]
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  have hcrj := InternalGraphCompositionFunctionalityProof.renameInto hcr j Theta hj
  simp only [graph2Rename,sucRelabel,InternalTagArithmeticSyntaxProof.numeralRelabel] at hrj hdj hmj hcrj
  exact observed (node.relabel j) (param.relabel j) (deps.relabel j) (child.relabel j)
    (childRank.relabel j) (f.relabel j) (ys 0) (ys 1) (ys 2) (ys 3)
    hrj hdj hmj hcrj (hq 0) (hq 1) (hq 2) (hq 3)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.DependencyPositiveProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.DependencyPositiveProof
