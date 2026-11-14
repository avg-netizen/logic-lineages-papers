module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc sucRelabel)
open InternalOriginalUniformVertexPathSupportProof (ternaryValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem internalZero : Targets.InternalZero := by
  intro body alpha Delta R D G seed param
  exact recursionZeroValue (InternalAcceptance.constantZero 2) (step R D G)
    z ![seed,param] (constantZeroValue ![seed,param])

theorem stepGraph (R D : Program 2) (G : Program 3)
    (i old seed param rankValue depth nodes out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 R rankValue seed param)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth i rankValue)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList D) nodes depth seed param)))
    (hs : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out nodes old param))) :
    Nonempty (Derivation body Delta (programGraph (step R D G) out ![i,old,seed,param])) := by
  let xs : Fin 4 → OTerm alpha := ![i,old,seed,param]
  have hr' := binaryValue R (.projection 2) (.projection 3) rankValue seed param xs
    hr (projectionValue 2 xs) (projectionValue 3 xs)
  have hd' := binaryValue InternalEqualityTest.subtract (.projection 0) (rank R)
    depth i rankValue xs hd (projectionValue 0 xs) hr'
  have hf' := ternaryValue (ExchangeFrontier.bindList D) (remaining R) (.projection 2) (.projection 3)
    nodes depth seed param xs hf hd' (projectionValue 2 xs) (projectionValue 3 xs)
  exact ternaryValue (ExchangeGraphStage.stage D G) (frontier R D) (.projection 1) (.projection 3)
    out nodes old param xs hs hf' (projectionValue 1 xs) (projectionValue 3 xs)

theorem successorValue (R D : Program 2) (G : Program 3)
    (i seed param old rankValue depth nodes out : OTerm alpha)
    (hprev : Nonempty (Derivation body Delta (graph3 (graph R D G) old i seed param)))
    (hr : Nonempty (Derivation body Delta (graph2 R rankValue seed param)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth i rankValue)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList D) nodes depth seed param)))
    (hs : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out nodes old param))) :
    Nonempty (Derivation body Delta (graph3 (graph R D G) out (suc i) seed param)) := by
  have hv := stepGraph R D G i old seed param rankValue depth nodes out hr hd hf hs
  unfold graph3 graph programGraph at hprev ⊢
  unfold programGraph at hv
  exact InternalRecursionGraphSuccessorIntroductionProof.recursionSuccessorIntroduction
    Delta (OrdinaryArithmetic.graphFormula (InternalAcceptance.constantZero 2))
    (OrdinaryArithmetic.graphFormula (step R D G)) out i old ![seed,param] hprev hv

theorem internalSuccessor : Targets.InternalSuccessor := by
  intro body alpha Delta R D G i seed param old rankValue depth nodes out hprev hr hd hf
  constructor
  · intro ho
    apply programCases (ExchangeGraphStage.stage D G) (Fin.cons nodes (Fin.cons old (Fin.cons param Fin.elim0))) _
    intro beta j Theta value hj hv
    rw [graph3Rename]
    simp only [consTermRename,emptyRename] at hv
    have hprev' := renameInto hprev j Theta hj
    rw [graph3Rename] at hprev'
    have hr' := renameInto hr j Theta hj
    rw [graph2Rename] at hr'
    have hd' := renameInto hd j Theta hj
    rw [graph2Rename] at hd'
    have hf' := renameInto hf j Theta hj
    rw [graph3Rename] at hf'
    have ho' := renameInto ho j Theta hj
    simp only [graph3Rename,sucRelabel] at ho'
    have hn := successorValue R D G (i.relabel j) (seed.relabel j) (param.relabel j)
      (old.relabel j) (rankValue.relabel j) (depth.relabel j) (nodes.relabel j) value hprev' hr' hd' hf' hv
    have hu := valueUnique (graph R D G) value (out.relabel j)
      ![suc (i.relabel j),seed.relabel j,param.relabel j] hn ho'
    exact outputTransport (ExchangeGraphStage.stage D G) value (out.relabel j)
      ![nodes.relabel j,old.relabel j,param.relabel j] hu hv
  · exact successorValue R D G i seed param old rankValue depth nodes out hprev hr hd hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.InternalProof
