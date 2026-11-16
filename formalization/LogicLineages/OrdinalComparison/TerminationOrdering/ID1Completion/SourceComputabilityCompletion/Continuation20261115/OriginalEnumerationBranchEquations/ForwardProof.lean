module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.BackwardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.ForwardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationStepPeelSupportProof (andIntro)
open OriginalEnumerationRecursionInterface
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def priorValue (n : Nat) : Program 2 := .composition (OriginalEnumerationRecursion.enumeration n) ![priorNode,.projection 1]
def openedValue (n : Nat) : Program 2 := .composition (OriginalEnumerationRecursion.enumeration n) ![openedNode,.projection 1]
def valueTail (n : Nat) : Program 2 := .composition InternalListCodec.consCode ![openedValue n,InternalAcceptance.constantZero 2]
def valuePair (n : Nat) : Program 2 := .composition InternalListCodec.consCode ![priorValue n,valueTail n]
def layerValue (n : Nat) : Program 2 := .composition (positiveLayer n) ![.projection 0,valuePair n,.projection 1]
def queries (n : Nat) : Fin 9 → Program 2 :=
  ![priorNode,openedNode,priorValue n,openedValue n,DependencyPositiveProof.tailProgram,
    positiveDependencies,valueTail n,valuePair n,layerValue n]

theorem atQueries (n : Nat) (node param vb f ts hs ls tb p2 p3 out : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node vb (suc f))))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ts p2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p2 hs p3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3 ls tb)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out node param)))
    (ys : Fin 9 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries n i) (ys i) ![node,param]))) :
    Nonempty (Derivation body Delta (Targets.successorOutput n out param vb f ts hs ls tb)) := by
  have hbound := SelectorProof.boundAt node param vb (suc f) hn
  have hfuel := SelectorProof.previousAt node param f (SelectorProof.rankAt node param vb (suc f) hn)
  have ha := binaryRecover InternalPairing.pairing bound previousFuel (ys 0) vb f ![node,param]
    (hq 0) hbound hfuel
  have hsb : Nonempty (Derivation body Delta
      (graph2 (.composition .succ (fun _ : Fin 1 => bound)) (suc vb) node param)) :=
    unaryValue .succ bound (suc vb) vb ![node,param]
      (successorValue (Fin.cons vb Fin.elim0)) hbound
  have hc := binaryRecover InternalPairing.pairing (.composition .succ (fun _ : Fin 1 => bound))
    previousFuel (ys 1) (suc vb) f ![node,param] (hq 1) hsb hfuel
  have hea := binaryRecover (OriginalEnumerationRecursion.enumeration n) priorNode (.projection 1)
    (ys 2) (ys 0) param ![node,param] (hq 2) (hq 0) (projectionValue 1 ![node,param])
  have hec := binaryRecover (OriginalEnumerationRecursion.enumeration n) openedNode (.projection 1)
    (ys 3) (ys 1) param ![node,param] (hq 3) (hq 1) (projectionValue 1 ![node,param])
  have ht := binaryRecover InternalListCodec.consCode openedNode (InternalAcceptance.constantZero 2)
    (ys 4) (ys 1) z ![node,param] (hq 4) (hq 1)
    (InternalAcceptanceConjunctionProof.constantZeroValue ![node,param])
  have hd := binaryRecover InternalListCodec.consCode priorNode DependencyPositiveProof.tailProgram
    (ys 5) (ys 0) (ys 4) ![node,param] (hq 5) (hq 0) (hq 4)
  have hr := binaryRecover InternalListCodec.consCode (openedValue n) (InternalAcceptance.constantZero 2)
    (ys 6) (ys 3) z ![node,param] (hq 6) (hq 3)
    (InternalAcceptanceConjunctionProof.constantZeroValue ![node,param])
  have hv := binaryRecover InternalListCodec.consCode (priorValue n) (valueTail n)
    (ys 7) (ys 2) (ys 6) ![node,param] (hq 7) (hq 2) (hq 6)
  have hpos : Nonempty (Derivation body Delta (graph3 (positiveLayer n) (ys 8) node (ys 7) param)) := by
    apply InternalAcceptanceSupportProof.compositionRecover (positiveLayer n)
      ![.projection 0,valuePair n,.projection 1] (ys 8) ![node,param] ![node,ys 7,param] (hq 8)
    intro i
    fin_cases i
    · exact projectionValue 0 ![node,param]
    · exact hq 7
    · exact projectionValue 1 ![node,param]
  have hl := CombineScalarProof.layerRecover n node (ys 7) param vb (suc f) ts hs ls tb p2 p3
    (ys 2) (ys 3) (ys 8) hn hp h2 h3
    (AnswerPairProof.firstLookup (ys 7) (ys 2) (ys 6) hv)
    (AnswerPairProof.secondLookup (ys 7) (ys 2) (ys 6) (ys 3) hv hr) hpos
  have hvalue := ValueProof.atValues n node param vb f ts hs ls tb p2 p3
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 5) (ys 4) (ys 7) (ys 6) (ys 8)
    hn hp h2 h3 ha hc hea hec ht hd hr hv hl
  have heq := valueUnique (OriginalEnumerationRecursion.enumeration n) (ys 8) out ![node,param] hvalue he
  have hlout := outputTransport (OriginalEnumerationConstructorLayer.layer n) (ys 8) out
    ![ts,hs,ls,tb,vb,ys 2,ys 3] heq hl
  exact WitnessProof.introduce n out param vb f ts hs ls tb ![ys 0,ys 1,ys 2,ys 3]
    (andIntro (andIntro (andIntro (andIntro ha hc) hea) hec) hlout)

theorem forward (n : Nat) (node param vb f ts hs ls tb p2 p3 out : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node vb (suc f))))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ts p2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p2 hs p3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3 ls tb)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out node param))) :
    Nonempty (Derivation body Delta (Targets.successorOutput n out param vb f ts hs ls tb)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (queries n) ![node,param] _
  intro beta j ys Theta hj hq
  have hxs : (fun i : Fin 2 => (![node,param] i).relabel j) = ![node.relabel j,param.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hxs] at hq
  rw [WitnessProof.successorRename]
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,sucRelabel] at hnj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph2Rename,sucRelabel] at hpj
  have h2j := InternalGraphCompositionFunctionalityProof.renameInto h2 j Theta hj
  simp only [graph2Rename,sucRelabel] at h2j
  have h3j := InternalGraphCompositionFunctionalityProof.renameInto h3 j Theta hj
  simp only [graph2Rename,sucRelabel] at h3j
  have hej := InternalGraphCompositionFunctionalityProof.renameInto he j Theta hj
  simp only [graph2Rename,sucRelabel] at hej
  exact atQueries n (node.relabel j) (param.relabel j) (vb.relabel j) (f.relabel j)
    (ts.relabel j) (hs.relabel j) (ls.relabel j) (tb.relabel j) (p2.relabel j) (p3.relabel j)
    (out.relabel j) hnj hpj h2j h3j hej ys hq
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.ForwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.ForwardProof
