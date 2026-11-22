module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasurePairCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowBumpProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureArgumentProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderIntroduction)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (trans congSuc addZero addSucc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename moveReport)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (measurePair)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTermPartProof (ordinaryRename)
open NumberedWindowInternalCoverLambdaMeasureRowTargets (lambdaBump)
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter)
open NumberedWindowInternalCoverLambdaSelectedMeasurePairCasesProof (codePairCases)
open NumberedWindowInternalCoverLambdaMeasureRowBumpProof (exact_OpenCoverLambdaBumpPair)
open NumberedWindowInternalCoverOrdinaryMeasureCutProof (exact_OpenCoverOrdinaryMeasureCut)
open NumberedWindowInternalCoverOrdinaryMeasureTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem selfWeak (d : OTerm α) : Nonempty (Derivation body Γ (ltF d (suc d))) := by
  apply actualOriginalOrderIntroduction body α Γ d (suc d) z
  rw [onEquality]
  exact ⟨trans (addSucc d z) (congSuc (addZero d))⟩

/-- Match the real fallback callback at the genuine argument code to the
argument selector used in the actual accepted numeric bump graph. -/
theorem exact_OpenOrdinaryBumpFromArgument (A : Program 1) (h a p m : OTerm α)
    (cut : Nonempty (Derivation body Γ
      (unary (ordinarySelectedBump A) p (ordinaryKey h a))))
    (arg : Nonempty (Derivation body Γ (unary (selectedArgsMeasure A) m a))) :
    Nonempty (Derivation body Γ (unary lambdaBump p m)) := by
  let raw := ordinaryKey h a
  have tag : Nonempty (Derivation body Γ (unary (literal 1 4) (numeral 4) raw)) := literalGraph 4 ![raw]
  have selected := (packedNode (literal 1 4) (numeral 4) [h,a] tag).2.2.1
  have exactArg : Nonempty (Derivation body Γ (unary (ordinaryArgumentCode A) m raw)) := by
    apply compositionValue (selectedArgsMeasure A) (fun _ : Fin 1 => field 1) m ![raw] ![a] arg
    intro j
    obtain rfl := Fin.eq_zero j
    exact selected
  apply compositionRecover lambdaBump (fun _ : Fin 1 => ordinaryArgumentCode A) p ![raw] ![m] cut
  intro j
  obtain rfl := Fin.eq_zero j
  exact exactArg

private theorem reindex {β : Type} (j : α → β) (Δ : List (Formula β))
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) (P : Program 1) (p h a : OTerm α)
    (source : Nonempty (Derivation body Γ (unary P p (ordinaryKey h a)))) :
    Nonempty (Derivation body Δ (unary P (p.relabel j) (ordinaryKey (h.relabel j) (a.relabel j)))) := by
  have renamed := moveReport j Δ keep P p (ordinaryKey h a) source
  rw [ordinaryRename] at renamed
  exact renamed

theorem exact_OpenCoverOrdinaryArgumentPair : ExactOpenCoverOrdinaryArgumentPair := by
  intro M A body α Γ h a p Q parent next
  let L := ordinarySelectedBump A
  have cut := exact_OpenCoverOrdinaryMeasureCut M A body α Γ h a p parent
  apply programCases (selectedArgsMeasure A) ![a] Q
  intro β j Δ m keep arg
  rw [inputsRename] at arg
  have bump := exact_OpenOrdinaryBumpFromArgument A (h.relabel j) (a.relabel j) (p.relabel j) m
    (reindex j Δ keep L p h a cut) arg
  apply codePairCases m (Q.relabel j)
  intro γ k Ξ d width retain pair
  have carried : ∀ f ∈ Γ, f.relabel (k ∘ j) ∈ Ξ := by
    intro f hf
    rw [← formulaRelabelComposition j k f]
    exact retain (f.relabel j) (keep f hf)
  have sameArg := moveReport k Ξ retain (selectedArgsMeasure A) m (a.relabel j) arg
  have sameBump := moveReport k Ξ retain lambdaBump (p.relabel j) m bump
  simp only [Term.relabel_relabel] at sameArg sameBump
  have measured := exact_OpenCoverLambdaBumpPair body γ Ξ (p.relabel (k ∘ j)) (m.relabel k)
    d width pair sameBump
  rw [formulaRelabelComposition j k Q]
  exact next γ (k ∘ j) Ξ (m.relabel k) d width carried sameArg pair measured (selfWeak d) (selfWeak width)

#print axioms exact_OpenOrdinaryBumpFromArgument
#print axioms exact_OpenCoverOrdinaryArgumentPair

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureArgumentProof
