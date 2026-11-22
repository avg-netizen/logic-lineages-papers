module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename outputTransport projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (congSuc symm)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseScalarEdge (edgeGraph edge4 exchangeTape)
open NumberedWindowInternalSparseDirectedSeen (edgeTape acceptEdge)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (casesLeast)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange compareOptions)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets (directedX)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets (thinPairedExchange thinSwapExchange)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalCoverCombinedRestrictedWrapperReportProof (exact_OpenCoverThinMatchingWindowReport)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowInternalSparseAdjacentMinimumChecks (exact_MutualEdgeMinimumEquality)
open NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureProof
  (exact_OpenCoverCombinedRestrictedPairedSharedMeasureEdge)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationProof (exact_RoundApplicationLeastAt)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationTargets
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)}

private theorem edgeRename {α β : Type} (X : Program 2) (W : Program 3) (ctx ty a b : OTerm α)
    (j : α → β) :
    (edgeGraph X W ctx ty a b).relabel j =
      edgeGraph X W (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j) := by
  simp only [edgeGraph,programRename,edgeTape,quadInputsRename,sucRelabel,zRelabel]

/-- An accepted edge of the guarded paired exchange over `D` gives the edge of
`D` itself in both directions, with the same two windows. -/
theorem pairedParentEdges {α : Type} {Γ : List (Formula α)} (C : Program 3) (s : Settings)
    (D : Program 2) (W : Program 3) (ctx ty w k : OTerm α)
    (e : Nonempty (Derivation body Γ
      (acceptEdge (edge4 (guardedExchange C s (thinPairedExchange D)) W) ctx ty w k))) :
    Nonempty (Derivation body Γ (edgeGraph D W ctx ty w k)) ∧
      Nonempty (Derivation body Γ (edgeGraph D W ctx ty k w)) := by
  let X := guardedExchange C s (thinPairedExchange D)
  obtain ⟨e⟩ := e
  obtain ⟨lawX⟩ := exact_OpenPackedScalarEdge X W body α Γ ctx ty w k
  have calls := Derivation.implicationElimination (Derivation.conjunctionLeft lawX) e
  have windows := Derivation.conjunctionRight calls
  obtain ⟨g⟩ := conjunctionRecover (thinPairedExchange D) (compareOptions C s) (exchangeTape w k)
    ⟨Derivation.conjunctionLeft calls⟩
  obtain ⟨pp⟩ := conjunctionRecover D (thinSwapExchange D) (exchangeTape w k) ⟨Derivation.conjunctionLeft g⟩
  have rev : Nonempty (Derivation body Γ (programGraph D (suc z) (exchangeTape k w))) := by
    apply compositionRecover D ![.projection 1,.projection 0] (suc z) (exchangeTape w k) ![k,w]
      ⟨Derivation.conjunctionRight pp⟩
    intro i
    refine Fin.cases ?_ (fun t => ?_) i
    · exact projectionValue 1 (exchangeTape w k)
    · obtain rfl := Fin.eq_zero t
      exact projectionValue 0 (exchangeTape w k)
  obtain ⟨rev⟩ := rev
  obtain ⟨lawF⟩ := exact_OpenPackedScalarEdge D W body α Γ ctx ty w k
  obtain ⟨lawR⟩ := exact_OpenPackedScalarEdge D W body α Γ ctx ty k w
  exact ⟨⟨Derivation.implicationElimination (Derivation.conjunctionRight lawF)
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft pp) windows)⟩,
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight lawR)
      (Derivation.conjunctionIntroduction rev (Derivation.conjunctionIntroduction
        (Derivation.conjunctionRight windows) (Derivation.conjunctionLeft windows)))⟩⟩

/-- Re-derived from the (private) helper of the PairedCommonLeast proof. -/
private theorem shareLeast {α : Type} {Γ : List (Formula α)}
    (C : Program 3) (s : Settings) (baseX : Program 2) (W : Program 3) (ctx ty a b x : OTerm α)
    (ab : Nonempty (Derivation body Γ (edgeGraph (guardedExchange C s baseX) W ctx ty a b)))
    (ba : Nonempty (Derivation body Γ (edgeGraph (guardedExchange C s baseX) W ctx ty b a)))
    (la : Nonempty (Derivation body Γ (leastGraph C (guardedExchange C s baseX) W s ctx ty a x)))
    (hb : Nonempty (Derivation body Γ (hasLeast C (guardedExchange C s baseX) W s ctx ty b))) :
    Nonempty (Derivation body Γ (leastGraph C (guardedExchange C s baseX) W s ctx ty b x)) := by
  let X := guardedExchange C s baseX
  apply casesLeast C X W s ctx ty b (leastGraph C X W s ctx ty b x) hb
  intro β i Θ y keep ly
  rw [leastRename]
  have ab' := renameInto ab i Θ keep
  have ba' := renameInto ba i Θ keep
  have la' := renameInto la i Θ keep
  rw [edgeRename] at ab' ba'
  rw [leastRename] at la'
  obtain ⟨ab'⟩ := ab'
  obtain ⟨ba'⟩ := ba'
  obtain ⟨la'⟩ := la'
  obtain ⟨ly⟩ := ly
  obtain ⟨law⟩ := exact_MutualEdgeMinimumEquality C s baseX W body β Θ
    (ctx.relabel i) (ty.relabel i) (a.relabel i) (b.relabel i) (x.relabel i) y
  have eq : Derivation body Θ (eqn (x.relabel i) y) :=
    Derivation.implicationElimination law (Derivation.conjunctionIntroduction
      (Derivation.conjunctionIntroduction la' ly) (Derivation.conjunctionIntroduction ab' ba'))
  exact outputTransport (packedLeastProgram C X W s) (suc y) (suc (x.relabel i))
    ![ctx.relabel i,ty.relabel i,b.relabel i] ⟨congSuc (symm eq)⟩ ⟨ly⟩

theorem exact_CombinedApplicationLeastStep : ExactCombinedApplicationLeastStep := by
  intro V TV M M0 B T base s body α Γ ctx dom cod arg μ m w k P W X syn ty argument e mw mk lw
  have edges := pairedParentEdges P.cover s (directedX base P.V) W ctx (rawCons dom cod) w k e
  have ab := exact_OpenCoverCombinedRestrictedPairedSharedMeasureEdge V TV M M0 B T base s body α Γ
    ctx dom cod w k arg μ syn ty argument edges.1 edges.2 mw mk
  have ba := exact_OpenCoverCombinedRestrictedPairedSharedMeasureEdge V TV M M0 B T base s body α Γ
    ctx dom cod k w arg μ syn ty argument edges.2 edges.1 mk mw
  obtain ⟨abd⟩ := ab
  obtain ⟨law⟩ := exact_OpenPackedScalarEdge X W body α Γ ctx cod
    (auxiliaryTerm dom cod w arg) (auxiliaryTerm dom cod k arg)
  have windows := Derivation.conjunctionRight
    (Derivation.implicationElimination (Derivation.conjunctionLeft law) abd)
  obtain ⟨rep⟩ := exact_OpenCoverThinMatchingWindowReport P.cover P.W P.V X s body α Γ ctx cod
    (auxiliaryTerm dom cod k arg) ⟨Derivation.conjunctionRight windows⟩
  exact shareLeast P.cover s (thinPairedExchange (directedX base P.V)) W ctx cod
    (auxiliaryTerm dom cod w arg) (auxiliaryTerm dom cod k arg) m ⟨abd⟩ ba lw
    ⟨Derivation.conjunctionRight rep⟩

theorem exact_CombinedApplicationEdgeStepAt : ExactCombinedApplicationEdgeStepAt := by
  intro V TV M M0 B T base s body α Γ ctx dom cod arg μ m P W X meas syn ty argument
  intro β j Δ w k keep e mw
  have syn' := renameInto syn j Δ keep
  have ty' := renameInto ty j Δ keep
  have argument' := renameInto argument j Δ keep
  simp only [conjunctionRename,unaryRename,sucRelabel,zRelabel] at syn' ty'
  rw [windowRename] at argument'
  rw [rawConsRename] at e
  obtain ⟨mwd⟩ := mw
  have mwm : Derivation body Δ (unary (selectedMeasure P.R) (μ.relabel j) w) :=
    Derivation.conjunctionLeft mwd
  have mwl : Derivation body Δ (leastGraph P.cover X W s (ctx.relabel j) (cod.relabel j)
      (auxiliaryTerm (dom.relabel j) (cod.relabel j) w (arg.relabel j)) (m.relabel j)) :=
    Derivation.conjunctionRight mwd
  obtain ⟨ed⟩ := e
  obtain ⟨pres⟩ := meas body β Δ (ctx.relabel j) (rawCons (dom.relabel j) (cod.relabel j)) (μ.relabel j) w k
  have mk := Derivation.implicationElimination pres (Derivation.conjunctionIntroduction ed mwm)
  obtain ⟨lk⟩ := exact_CombinedApplicationLeastStep V TV M M0 B T base s body β Δ (ctx.relabel j)
    (dom.relabel j) (cod.relabel j) (arg.relabel j) (μ.relabel j) (m.relabel j) w k syn' ty' argument'
    ⟨ed⟩ ⟨mwm⟩ ⟨mk⟩ ⟨mwl⟩
  exact ⟨Derivation.conjunctionIntroduction mk lk⟩

theorem exact_CombinedRoundApplicationLeast : ExactCombinedRoundApplicationLeast := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f arg μ m i vertices out k P W X meas syn ty argument
    mf lf round member
  have step := exact_CombinedApplicationEdgeStepAt V TV M M0 B T base s body α Γ ctx dom cod arg μ m
    meas syn ty argument
  obtain ⟨mf⟩ := mf
  obtain ⟨lf⟩ := lf
  exact exact_RoundApplicationLeastAt (edge4 X W) (selectedMeasure P.R) P.cover X W s body α Γ
    i vertices ctx (rawCons dom cod) f out k ctx cod dom cod arg μ m step
    ⟨Derivation.conjunctionIntroduction mf lf⟩ round member

#print axioms pairedParentEdges
#print axioms exact_CombinedApplicationLeastStep
#print axioms exact_CombinedApplicationEdgeStepAt
#print axioms exact_CombinedRoundApplicationLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedProof
