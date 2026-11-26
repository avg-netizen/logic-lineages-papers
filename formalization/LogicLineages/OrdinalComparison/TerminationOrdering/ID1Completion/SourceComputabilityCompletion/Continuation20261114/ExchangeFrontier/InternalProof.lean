module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphStage.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.RecursionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem flattenStepGraph (D : Program 2) (node rest param deps out : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 D deps node param)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out deps rest))) :
    Nonempty (Derivation body Delta (programGraph (flattenStep D) out ![node,rest,param])) := by
  let xs : Fin 3 → OTerm alpha := ![node,rest,param]
  have hd' := binaryValue D (.projection 0) (.projection 2) deps node param xs hd
    (projectionValue 0 xs) (projectionValue 2 xs)
  exact binaryValue InternalApplicationValidityStackAppend.append
    (.composition D ![.projection 0,.projection 2]) (.projection 1) out deps rest xs
    ha hd' (projectionValue 1 xs)

theorem internalFlattenCons : Targets.InternalFlattenCons := by
  intro body alpha Delta D nodes node tail param deps rest out hc hd hr ha
  exact InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 1) (flattenStep D)
    nodes node tail rest out (Fin.cons param Fin.elim0) hc hr
    (flattenStepGraph D node rest param deps out hd ha)

theorem successorValue (D : Program 2) (depth seed param previous out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph3 (bindList D) previous depth seed param)))
    (hf : Nonempty (Derivation body Delta (graph2 (flatten D) out previous param))) :
    Nonempty (Derivation body Delta (graph3 (bindList D) out (suc depth) seed param)) := by
  have hs : Nonempty (Derivation body Delta (programGraph (bindStep D) out ![depth,previous,seed,param])) :=
    binaryValue (flatten D) (.projection 1) (.projection 3) out previous param
      ![depth,previous,seed,param] hf (projectionValue 1 ![depth,previous,seed,param])
      (projectionValue 3 ![depth,previous,seed,param])
  unfold graph3 bindList programGraph at hr ⊢
  unfold programGraph at hs
  exact InternalRecursionGraphSuccessorIntroductionProof.recursionSuccessorIntroduction
    Delta (OrdinaryArithmetic.graphFormula singleton) (OrdinaryArithmetic.graphFormula (bindStep D))
    out depth previous ![seed,param] hr hs

theorem internalBindSuccessor : Targets.InternalBindSuccessor := by
  intro body alpha Delta D depth seed param previous out hr
  constructor
  · intro ho
    apply programCases (flatten D) (Fin.cons previous (Fin.cons param Fin.elim0)) _
    intro beta j Theta value hj hv
    rw [graph2Rename]
    simp only [consTermRename,emptyRename] at hv
    have hr' := renameInto hr j Theta hj
    rw [graph3Rename] at hr'
    have ho' := renameInto ho j Theta hj
    simp only [graph3Rename,sucRelabel] at ho'
    have hn := successorValue D (depth.relabel j) (seed.relabel j) (param.relabel j)
      (previous.relabel j) value hr' hv
    have hu := valueUnique (bindList D) value (out.relabel j)
      ![suc (depth.relabel j),seed.relabel j,param.relabel j] hn ho'
    exact outputTransport (flatten D) value (out.relabel j)
      ![previous.relabel j,param.relabel j] hu hv
  · exact successorValue D depth seed param previous out hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier.InternalProof
