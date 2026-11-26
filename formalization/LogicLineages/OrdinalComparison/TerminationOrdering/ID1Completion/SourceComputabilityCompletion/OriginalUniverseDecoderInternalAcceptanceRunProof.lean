module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationSaturationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceRunProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof
open OriginalUniverseDecoder OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel
open OriginalTypedDecoderInternalFuel (workFuel WorkFuelGraph)
open OriginalUniverseDecoderInternalFuelIterationSyntaxProof
open OriginalUniverseDecoderInternalFuelIterationWorkProof
open OriginalUniverseDecoderInternalFuelIterationProof
open OriginalUniverseDecoderInternalFuelNumericSupportProof
open OriginalTypedDecoderInternalFuelIterationTerminalProof (successPair)
open OriginalLambdaConstructorGraphSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem successfulWorkIntro (H : Program 1) (M W : Program 2) (count work state c : OTerm α)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hr : Nonempty (Derivation body Gamma (graph3 (iterate H M W) (numeral 2) count state c))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H M W count work c)) :=
  workRunIntro H M W (numeral 2) count work state c hs hr

theorem successfulWorkAt (H : Program 1) (M W : Program 2) (count work state c : OTerm α)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hr : Nonempty (Derivation body Gamma (SuccessfulWork H M W count work c))) :
    Nonempty (Derivation body Gamma (graph3 (iterate H M W) (numeral 2) count state c)) :=
  workRunAt H M W (numeral 2) count work state c hs hr

theorem countTransport (H : Program 1) (M W : Program 2) (count other work c : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn count other)))
    (h : Nonempty (Derivation body Gamma (SuccessfulWork H M W count work c))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H M W other work c)) :=
  workRunCountTransport H M W (numeral 2) count other work c he h

theorem workTransport (H : Program 1) (M W : Program 2) (count work other c : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn work other)))
    (h : Nonempty (Derivation body Gamma (SuccessfulWork H M W count work c))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H M W count other c)) :=
  workRunWorkTransport H M W (numeral 2) count work other c he h

theorem zeroWork (H : Program 1) (M W : Program 2) (work c : OTerm α)
    (h : Nonempty (Derivation body Gamma (SuccessfulWork H M W z work c))) :
    Nonempty (Derivation body Gamma (eqn work z)) := by
  apply workRunCases H M W (numeral 2) z work c _ h
  intro β j Delta state _ hs hr
  simp only [eqnRelabel,zRelabel]
  simp only [zRelabel,numeral,sucRelabel,zRelabel] at hr
  obtain ⟨he⟩ := repeatZeroRecover (transition H M W) (numeral 2) state (c.relabel j) hr
  have hw := headTransport InternalUnpair.right (work.relabel j) state (numeral 2) Fin.elim0
    ⟨symm he⟩ (pairRight state (numeral 1) (work.relabel j) hs)
  exact valueUnique InternalUnpair.right (work.relabel j) z (Fin.cons (numeral 2) Fin.elim0)
    hw (pairRight (numeral 2) (numeral 1) z successPair)

theorem nilSuccess (H : Program 1) (M W : Program 2) (count c : OTerm α) :
    Nonempty (Derivation body Gamma (SuccessfulWork H M W count z c)) :=
  OriginalUniverseDecoderInternalFuelIterationTerminalProof.nilSuccessful H M W count c

theorem successPadding (H : Program 1) (M W : Program 2) (count padding work c : OTerm α)
    (h : Nonempty (Derivation body Gamma (SuccessfulWork H M W count work c))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H M W (OrdinaryArithmetic.addTerm count padding) work c)) :=
  OriginalUniverseDecoderInternalFuelIterationSaturationSupportProof.successfulPadding H M W count padding work c h

theorem failureImpossible (H : Program 1) (M W : Program 2) (count c : OTerm α)
    (h : Nonempty (Derivation body Gamma (graph3 (iterate H M W) (numeral 2) count z c))) :
    Nonempty (Derivation body Gamma (⊥ : Formula α)) := by
  obtain ⟨he⟩ := valueUnique (iterate H M W) (numeral 2) z
    ![count,z,c] h (iterateFailure H M W count c)
  exact ⟨sucNeZeroApply he⟩

/-- Any successful finite guarded run pays acceptance at the unchanged
original raw+1 work weight. The SAME c remains fixed throughout padding. -/
theorem successfulAccepted (H : Program 1) (M W : Program 2) (count work c : OTerm α)
    (hr : Nonempty (Derivation body Gamma (SuccessfulWork H M W count work c))) :
    Nonempty (Derivation body Gamma (WorkAccepted H M W work c)) := by
  apply programCases workFuel (Fin.cons work Fin.elim0) _
  intro β j Delta required hj hf
  rw [workAcceptedRename]
  simp only [consTermRename,emptyRename] at hf
  have hr' := renameInto hr j Delta hj
  rw [successfulWorkRename] at hr'
  exact OriginalUniverseDecoderInternalFuelIterationSaturationProof.saturatedForward H M W
    required (OrdinaryArithmetic.addTerm (count.relabel j) required) (work.relabel j) (c.relabel j) hf
    (InternalUnpairReverseBoundsArithmeticProof.rightWeakAdd (count.relabel j) required)
    (successPadding H M W (count.relabel j) required (work.relabel j) (c.relabel j) hr')

theorem nilAccepted (H : Program 1) (M W : Program 2) (c : OTerm α) :
    Nonempty (Derivation body Gamma (WorkAccepted H M W (z : OTerm α) c)) :=
  acceptedIntro H M W z z c OriginalTypedDecoderInternalFuelSupportProof.nilValue (nilSuccess H M W z c)

theorem acceptedWorkTransport (H : Program 1) (M W : Program 2) (work other c : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn work other)))
    (ha : Nonempty (Derivation body Gamma (WorkAccepted H M W work c))) :
    Nonempty (Derivation body Gamma (WorkAccepted H M W other c)) := by
  apply acceptedCases H M W work c _ ha
  intro β j Delta count hj hf hr
  rw [workAcceptedRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact successfulAccepted H M W count (other.relabel j) (c.relabel j)
    (workTransport H M W count (work.relabel j) (other.relabel j) (c.relabel j) he' hr)

theorem successOnePadding (H : Program 1) (M W : Program 2) (count work c : OTerm α)
    (h : Nonempty (Derivation body Gamma (SuccessfulWork H M W count work c))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H M W (suc count) work c)) := by
  have he : Derivation body Gamma (eqn (OrdinaryArithmetic.addTerm count (suc z)) (suc count)) :=
    InternalTagArithmeticSupportProof.trans (InternalTagArithmeticSupportProof.addSucc count z)
      (InternalTagArithmeticSupportProof.congSuc (InternalTagArithmeticSupportProof.addZero count))
  exact countTransport H M W (OrdinaryArithmetic.addTerm count (suc z)) (suc count) work c ⟨he⟩
    (successPadding H M W count (suc z) work c h)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceRunProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceRunProof
