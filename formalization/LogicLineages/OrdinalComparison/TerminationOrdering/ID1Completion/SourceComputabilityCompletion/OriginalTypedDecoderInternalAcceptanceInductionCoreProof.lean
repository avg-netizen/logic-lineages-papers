module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationValidityStackAppend InternalApplicationCertificateConstructors
open InternalApplicationValidityStackAppendSyntaxProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationValidityStackAppendListProof OriginalTypedDecoderInternalAcceptanceRunProof
open OriginalTypedDecoderInternalAcceptanceInductionSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalAdditionCancellationProof InternalOriginalOrderSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphChoiceProof
open InternalPositiveUnfoldingSupportProof InternalBetaTotalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open OriginalTypedDecoder OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalFuelIterationSyntaxProof
open OriginalTypedDecoderInternalFuelIterationWorkProof
open OriginalTypedDecoderInternalFuelIterationProof
open OriginalTypedDecoderInternalFuelIterationTerminalProof (successPair)
open OriginalLambdaConstructorGraphSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem withHyp {phi : Formula α} (h : Nonempty (Derivation body Gamma phi)) (p : Formula α) :
    Nonempty (Derivation body (p :: Gamma) phi) := by
  obtain ⟨h⟩ := h
  exact ⟨addHyp h p⟩

theorem formulaCases (p psi : Formula α)
    (hp : Nonempty (Derivation body (p :: Gamma) psi))
    (hn : Nonempty (Derivation body (p.not :: Gamma) psi)) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hn⟩ := hn
  exact ⟨disjunctionElimination (excludedMiddle p)
    (Derivation.implicationIntroduction hp) (Derivation.implicationIntroduction hn)⟩

theorem rowApply (H : Program 1) (count second frontWork suffix joined : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (appendRow H count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (SuccessfulWork H count frontWork)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H second suffix))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork H (OrdinaryArithmetic.addTerm count second) joined)) := by
  have h := actualFiniteUniversalElimination body α 4 Gamma (appendBody H count)
    (fun i => emb (![second,frontWork,suffix,joined] i)) hrow
  rw [appendBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := OriginalLambdaConstructorGraphSyntaxProof.andIntro ha (OriginalLambdaConstructorGraphSyntaxProof.andIntro hf hs)
  exact ⟨Derivation.implicationElimination h hp⟩

theorem emptyCore (H : Program 1) (count second frontWork suffix joined : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn frontWork z)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H second suffix))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork H (OrdinaryArithmetic.addTerm count second) joined)) := by
  have hz := headTransport append joined frontWork z (Fin.cons suffix Fin.elim0) he ha
  obtain ⟨hjoined⟩ := appendZeroRecover joined suffix hz
  have hpad := successPadding H second count suffix hs
  have hcount := countTransport H (add second count) (add count second) suffix
    ⟨commutativity second count⟩ hpad
  exact workTransport H (add count second) suffix joined ⟨symm hjoined⟩ hcount

theorem zeroCore (H : Program 1) (second frontWork suffix joined : OTerm α)
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (SuccessfulWork H z frontWork)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H second suffix))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork H (OrdinaryArithmetic.addTerm z second) joined)) :=
  emptyCore H z second frontWork suffix joined (zeroWork H frontWork hf) ha hs

theorem zeroRow (H : Program 1) :
    Nonempty (Derivation body Gamma (appendRow H z)) := by
  unfold appendRow
  apply actualFiniteUniversalIntroduction body α 4 Gamma
  let second : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let frontWork : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let suffix : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let joined : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  let A := graph2 append joined frontWork suffix ⊓
    (SuccessfulWork H z frontWork ⊓ SuccessfulWork H second suffix)
  obtain ⟨d⟩ := zeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) H second frontWork suffix joined
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  simpa only [appendBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionCoreProof
