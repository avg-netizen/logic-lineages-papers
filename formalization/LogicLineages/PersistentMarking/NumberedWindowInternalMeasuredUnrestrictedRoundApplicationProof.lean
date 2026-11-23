module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedApplicationLeastStepProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinLeastRepresentativeApplicationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalPairedPackedLeastChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredThinEdgeMeasureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoThinLiftGapProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedRoundApplicationProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (measuredFactoredExchange)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalAuxExchangeMemoThinLiftGapProof (pairRelabel)
open NumberedWindowInternalMeasuredThinEdgeMeasureProof (exact_OpenThinMeasuredEdgePreservesMeasure)
open NumberedWindowInternalMeasuredUnrestrictedApplicationLeastStepProof
open NumberedWindowInternalOriginalPairedPackedLeastChecks
open NumberedWindowInternalThinLeastRepresentativeApplicationProof
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationTargets

private theorem arrowRename {α β : Type} (dom cod : OTerm α) (j : α → β) :
    (rawCons dom cod).relabel j = rawCons (dom.relabel j) (cod.relabel j) := by
  simp only [rawCons,sucRelabel,pairRelabel]

/-- Precisely the typed-parent data needed for this original unrestricted
application transport, at each genuine open exchange and the fixed argument. -/
def ParentWindowsAt (E : Program 4) (W : Program 3) (B : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (ctx dom cod arg : OTerm α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (f g : OTerm β),
    (∀ p ∈ Γ, p.relabel j ∈ Δ) →
    Nonempty (Derivation B Δ
      (acceptEdge E (ctx.relabel j) (rawCons (dom.relabel j) (cod.relabel j)) f g)) →
    Nonempty (Derivation B Δ
      (windowAt W (ctx.relabel j) (cod.relabel j) (auxiliaryTerm (dom.relabel j) (cod.relabel j) f (arg.relabel j)))) ∧
    Nonempty (Derivation B Δ
      (windowAt W (ctx.relabel j) (cod.relabel j) (auxiliaryTerm (dom.relabel j) (cod.relabel j) g (arg.relabel j))))

theorem exact_OpenUnrestrictedMeasuredMotiveStep (s : Settings) (base : Program 2) (V baseM : Program 1)
    (P : Program 2) (G baseW : Program 3)
    (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod arg μ m : OTerm α) :
    let M := selectedMeasure (measureUpdate baseM P)
    let C := factoredCover V M G
    let W := window C s baseW V
    let X := measuredFactoredExchange s base V baseM P G
    let E := edge4 X W
    ParentWindowsAt E W B Γ ctx dom cod arg →
    ApplicationEdgeStepAt E M C X W s B Γ ctx (rawCons dom cod) ctx cod dom cod arg μ m := by
  intro M C W X E windows β j Δ f g keep edge held
  rw [arrowRename] at edge
  have typed := windows β j Δ f g keep edge
  obtain ⟨data⟩ := held
  obtain ⟨edge⟩ := edge
  obtain ⟨law⟩ := exact_OpenThinMeasuredEdgePreservesMeasure C s M (selected (step base V)) W B β Δ
    (ctx.relabel j) (rawCons (dom.relabel j) (cod.relabel j)) (μ.relabel j) f g
  have share := Derivation.implicationElimination law
    (Derivation.conjunctionIntroduction edge (Derivation.conjunctionLeft data))
  obtain ⟨moved⟩ := exact_OpenMeasuredUnrestrictedApplicationLeastStep
    exact_OriginalPhysicalCountLength exact_OriginalPhysicalCountStrict s base V baseM P G baseW B β Δ
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) f g (arg.relabel j) (m.relabel j)
    ⟨edge⟩ typed.1 typed.2 ⟨Derivation.conjunctionRight data⟩
  exact ⟨Derivation.conjunctionIntroduction share moved⟩

/-- The actual least of a function is a valid application
representative in the *unrestricted* exact measured original programs,
under the genuine typed parent-window law. No same-raw representative
premise or extra round, length, or selected-cover report is held. -/
theorem exact_OpenUnrestrictedMeasuredRepresentative (s : Settings) (base : Program 2)
    (V baseM : Program 1) (P : Program 2) (G baseW : Program 3)
    (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod f q arg μ m : OTerm α) :
    let M := selectedMeasure (measureUpdate baseM P)
    let C := factoredCover V M G
    let W := window C s baseW V
    let X := measuredFactoredExchange s base V baseM P G
    ParentWindowsAt (edge4 X W) W B Γ ctx dom cod arg →
    Nonempty (Derivation B Γ (unary M μ f)) →
    Nonempty (Derivation B Γ (leastGraph C X W s ctx (rawCons dom cod) f q)) →
    Nonempty (Derivation B Γ (leastGraph C X W s ctx cod (auxiliaryTerm dom cod f arg) m)) →
    Nonempty (Derivation B Γ (appMotive M C X W s ctx cod dom cod arg μ m q)) := by
  intro M C W X windows hμ klass applied
  obtain ⟨hμ⟩ := hμ
  obtain ⟨applied⟩ := applied
  exact exact_ThinLeastRepresentativeApplication C X W s M C X W s B α Γ ctx (rawCons dom cod) f q
    ctx cod dom cod arg μ m
    (exact_OpenUnrestrictedMeasuredMotiveStep s base V baseM P G baseW B α Γ ctx dom cod arg μ m windows)
    ⟨Derivation.conjunctionIntroduction hμ applied⟩ klass

#print axioms exact_OpenUnrestrictedMeasuredMotiveStep
#print axioms exact_OpenUnrestrictedMeasuredRepresentative
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedRoundApplicationProof
