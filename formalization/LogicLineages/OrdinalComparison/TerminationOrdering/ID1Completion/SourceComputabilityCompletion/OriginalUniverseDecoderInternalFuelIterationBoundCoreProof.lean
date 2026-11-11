module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationBoundSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationTerminalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelZeroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationBoundCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationBoundCoreProof
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
open OriginalUniverseDecoderInternalFuel
open OriginalTypedDecoderInternalFuel (WorkFuelGraph DecreasedOrFailed)
open OriginalUniverseDecoderInternalFuelIterationBoundSyntaxProof
open OriginalTypedDecoderInternalFuelIterationBoundSyntaxProof (weakBoundRename)
open OriginalTypedDecoderInternalFuelIterationBoundCoreProof (weakZero weakGapCases decreasedBound)
open OriginalUniverseDecoderInternalFuelIterationTerminalProof
open OriginalTypedDecoderInternalFuelZeroSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem rowApply (H : Program 1) (M contextWindow : Program 2) (count workCode required c : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (sufficientRow H M contextWindow count)))
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode)))
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required count))) :
    Nonempty (Derivation body Gamma (TerminatedWork H M contextWindow count workCode c)) := by
  have h := actualFiniteUniversalElimination body alpha 3 Gamma (sufficientBody H M contextWindow count)
    (fun i => emb (![workCode,required,c] i)) hrow
  rw [sufficientBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := andIntro hf hb
  exact ⟨Derivation.implicationElimination h hp⟩

theorem zeroCore (H : Program 1) (M contextWindow : Program 2) (workCode required c : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode)))
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required z))) :
    Nonempty (Derivation body Gamma (TerminatedWork H M contextWindow z workCode c)) := by
  obtain ⟨hw⟩ := zeroReflect required workCode hf (weakZero required hb)
  exact terminatedWorkTransport H M contextWindow z z workCode c ⟨symm hw⟩ (nilTerminated H M contextWindow z c)

theorem zeroRow (H : Program 1) (M contextWindow : Program 2) :
    Nonempty (Derivation body Gamma (sufficientRow H M contextWindow (z : OTerm alpha))) := by
  unfold sufficientRow
  apply actualFiniteUniversalIntroduction body alpha 3 Gamma
  let workCode : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let required : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let c : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let A := WorkFuelGraph required workCode ⊓ InternalPairingSumBounds.weakBound required z
  obtain ⟨h⟩ := zeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) H M contextWindow workCode required c
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [sufficientBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationBoundCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationBoundCoreProof
