module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationBoundSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationTerminalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelZeroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationBoundCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb sucRelabel zRelabel)
open InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalOriginalPairingOrderArithmeticProof (weakCases)
open InternalSquareRootArithmeticSupportProof (strictWeakTrans)
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalFuelIterationBoundSyntaxProof
open OriginalTypedDecoderInternalFuelIterationTerminalProof
open OriginalTypedDecoderInternalFuelZeroSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem weakZero (required : OTerm alpha)
    (h : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required z))) :
    Nonempty (Derivation body Gamma (eqn required z)) := by
  apply weakCases required z _ h
  · obtain ⟨hn⟩ := InternalApplicationValidityStackAppendTransitionProof.notLessZero
      (body := body) (Gamma := ltF required z :: Gamma) required
    exact ⟨Derivation.explosion
      (Derivation.implicationElimination hn (Derivation.hypothesis List.mem_cons_self))⟩
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

/-- A weak bound constructs the nonnegative spare count internally.
There is no native subtraction or external padding witness. -/
theorem weakGapCases (required count : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required count)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)) (gap : OTerm beta),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (eqn (add (required.relabel j) gap) (count.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply orderCases Gamma required (suc count) psi h
  intro beta j Delta gap hj he
  obtain ⟨he⟩ := he
  simp only [sucRelabel] at he
  exact step beta j Delta gap hj
    ⟨cancelSuc (trans (symm (addSucc (required.relabel j) gap)) he)⟩

theorem decreasedBound (next required count : OTerm alpha)
    (hd : Nonempty (Derivation body Gamma (InternalLessThan.strictLess next required)))
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required (suc count)))) :
    Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound next count)) :=
  strictWeakTrans next required (suc count) hd hb

theorem rowApply (H : Program 1) (count workCode required : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (sufficientRow H count)))
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode)))
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required count))) :
    Nonempty (Derivation body Gamma (TerminatedWork H count workCode)) := by
  have h := actualFiniteUniversalElimination body alpha 2 Gamma (sufficientBody H count)
    (fun i => emb (![workCode,required] i)) hrow
  rw [sufficientBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := andIntro hf hb
  exact ⟨Derivation.implicationElimination h hp⟩

theorem zeroCore (H : Program 1) (workCode required : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode)))
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required z))) :
    Nonempty (Derivation body Gamma (TerminatedWork H z workCode)) := by
  obtain ⟨hw⟩ := zeroReflect required workCode hf (weakZero required hb)
  exact terminatedWorkTransport H z z workCode ⟨symm hw⟩ (nilTerminated H z)

theorem zeroRow (H : Program 1) :
    Nonempty (Derivation body Gamma (sufficientRow H (z : OTerm alpha))) := by
  unfold sufficientRow
  apply actualFiniteUniversalIntroduction body alpha 2 Gamma
  let workCode : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let required : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  let A := WorkFuelGraph required workCode ⊓ InternalPairingSumBounds.weakBound required z
  obtain ⟨h⟩ := zeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) H workCode required
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [sufficientBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationBoundCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationBoundCoreProof
