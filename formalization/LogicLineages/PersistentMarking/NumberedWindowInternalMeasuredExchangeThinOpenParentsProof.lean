module

public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenComposeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenThinEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenParentsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalAuxMeasureOpenTargets (measureGraph)
open NumberedWindowInternalAuxMeasureOpenThinEvaluationProof (deriveValue)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (measuredFactoredExchange)
open NumberedWindowInternalMeasuredExchangeThinDefinitions (measuredExchange)
open NumberedWindowInternalMeasuredExchangeThinOpenTargets
open NumberedWindowInternalMeasuredExchangeThinOpenComposeProof (grammarTape putCover composeParents)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

structure ParentReports (V : Program 1) (X : Program 2) (body : Positive (Fin 1))
    (Γ : List (Formula α)) (a b : OTerm α) : Prop where
  forward : Nonempty (Derivation body Γ (accepted X a b))
  backward : Nonempty (Derivation body Γ (accepted X b a))
  syntaxA : Nonempty (Derivation body Γ (unary V (suc z) a))
  syntaxB : Nonempty (Derivation body Γ (unary V (suc z) b))

theorem renameUnary {β : Type} (p : Program 1) (out a : OTerm α) (j : α → β) (Δ : List (Formula β))
    (hJ : ∀ r ∈ Γ, r.relabel j ∈ Δ)
    (h : Nonempty (Derivation body Γ (unary p out a))) :
    Nonempty (Derivation body Δ (unary p (out.relabel j) (a.relabel j))) := by
  have moved := renameInto h j Δ hJ
  rwa [unaryRename] at moved

theorem renameAccepted {β : Type} (X : Program 2) (a b : OTerm α) (j : α → β) (Δ : List (Formula β))
    (hJ : ∀ r ∈ Γ, r.relabel j ∈ Δ)
    (h : Nonempty (Derivation body Γ (accepted X a b))) :
    Nonempty (Derivation body Δ (accepted X (a.relabel j) (b.relabel j))) := by
  have moved := renameInto h j Δ hJ
  simpa only [accepted,programRename,binaryInputsRename,zRelabel,sucRelabel] using moved

theorem renameReports {β : Type} {X : Program 2} {V : Program 1} {a b : OTerm α}
    (facts : ParentReports V X body Γ a b) (j : α → β) (Δ : List (Formula β))
    (hJ : ∀ r ∈ Γ, r.relabel j ∈ Δ) : ParentReports V X body Δ (a.relabel j) (b.relabel j) := by
  exact ⟨renameAccepted X a b j Δ hJ facts.forward,renameAccepted X b a j Δ hJ facts.backward,
    by simpa only [sucRelabel,zRelabel] using (renameUnary V (suc z) a j Δ hJ facts.syntaxA),
    by simpa only [sucRelabel,zRelabel] using (renameUnary V (suc z) b j Δ hJ facts.syntaxB)⟩

private theorem coverFromCommonMeasure (V M : Program 1) (X : Program 2) (G : Program 3) (s : Settings)
    (a b m : OTerm α) (facts : ParentReports V X body Γ a b)
    (ma : Nonempty (Derivation body Γ (unary M m a)))
    (mb : Nonempty (Derivation body Γ (unary M m b))) :
    Nonempty (Derivation body Γ
      (accepted (guardedExchange (factoredCover V M G) s (pairedExchange (measuredExchange M X))) a b)) := by
  let C := factoredCover V M G
  apply programCases G (grammarTape s m) _
  intro β j Δ out hJ grammar
  simp only [accepted,programRename,binaryInputsRename,sucRelabel,zRelabel]
  simp only [grammarTape,tripleInputsRename,numeralRename] at grammar
  have inputs := renameReports facts j Δ hJ
  have left := renameUnary M m a j Δ hJ ma
  have right := renameUnary M m b j Δ hJ mb
  have ca := putCover V M G s out (a.relabel j) (m.relabel j) inputs.syntaxA left grammar
  have cb := putCover V M G s out (b.relabel j) (m.relabel j) inputs.syntaxB right grammar
  exact composeParents M X C s (a.relabel j) (b.relabel j) (m.relabel j) out
    inputs.forward inputs.backward left right ca cb

private theorem commonAfterCombination (s : Settings) (baseX : Program 2) (V baseM : Program 1)
    (P : Program 2) (G : Program 3) (dom cod fn fn' arg m ma : OTerm α)
    (facts : ParentReports V (selected (step baseX V)) body Γ
      (auxiliaryTerm dom cod fn arg) (auxiliaryTerm dom cod fn' arg))
    (a : Nonempty (Derivation body Γ (measureGraph baseM P m fn)))
    (b : Nonempty (Derivation body Γ (measureGraph baseM P m fn')))
    (fixedArg : Nonempty (Derivation body Γ (measureGraph baseM P ma arg))) :
    Nonempty (Derivation body Γ (accepted (measuredFactoredExchange s baseX V baseM P G)
      (auxiliaryTerm dom cod fn arg) (auxiliaryTerm dom cod fn' arg))) := by
  let M := selectedMeasure (measureUpdate baseM P)
  apply programCases P ![m,ma] _
  intro β j Δ combined hJ compute
  simp only [accepted,programRename,binaryInputsRename,sucRelabel,zRelabel,auxiliaryRename]
  simp only [binaryInputsRename] at compute
  have f := renameReports facts j Δ hJ
  simp only [auxiliaryRename] at f
  have priorA := renameUnary M m fn j Δ hJ a
  have priorB := renameUnary M m fn' j Δ hJ b
  have arg' := renameUnary M ma arg j Δ hJ fixedArg
  have outA := deriveValue baseM P (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
    (m.relabel j) (ma.relabel j) combined priorA arg' compute
  have outB := deriveValue baseM P (dom.relabel j) (cod.relabel j) (fn'.relabel j) (arg.relabel j)
    (m.relabel j) (ma.relabel j) combined priorB arg' compute
  exact coverFromCommonMeasure V M (selected (step baseX V)) G s _ _ combined f outA outB

theorem fromCommonFunction (s : Settings) (baseX : Program 2) (V baseM : Program 1)
    (P : Program 2) (G : Program 3) (dom cod fn fn' arg m : OTerm α)
    (facts : ParentReports V (selected (step baseX V)) body Γ
      (auxiliaryTerm dom cod fn arg) (auxiliaryTerm dom cod fn' arg))
    (a : Nonempty (Derivation body Γ (measureGraph baseM P m fn)))
    (b : Nonempty (Derivation body Γ (measureGraph baseM P m fn'))) :
    Nonempty (Derivation body Γ (accepted (measuredFactoredExchange s baseX V baseM P G)
      (auxiliaryTerm dom cod fn arg) (auxiliaryTerm dom cod fn' arg))) := by
  let M := selectedMeasure (measureUpdate baseM P)
  apply programCases M ![arg] _
  intro β j Δ ma hJ compute
  simp only [accepted,programRename,binaryInputsRename,sucRelabel,zRelabel,auxiliaryRename]
  simp only [inputsRename] at compute
  have f := renameReports facts j Δ hJ
  simp only [auxiliaryRename] at f
  have priorA := renameUnary M m fn j Δ hJ a
  have priorB := renameUnary M m fn' j Δ hJ b
  exact commonAfterCombination s baseX V baseM P G (dom.relabel j) (cod.relabel j)
    (fn.relabel j) (fn'.relabel j) (arg.relabel j) (m.relabel j) ma f priorA priorB compute

end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenParentsProof
