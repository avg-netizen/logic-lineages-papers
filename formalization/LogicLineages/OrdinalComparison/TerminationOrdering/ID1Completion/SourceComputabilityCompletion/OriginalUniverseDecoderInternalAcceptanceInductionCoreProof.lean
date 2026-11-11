module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationValidityStackAppend InternalApplicationCertificateConstructors
open InternalApplicationValidityStackAppendSyntaxProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationValidityStackAppendListProof OriginalUniverseDecoderInternalAcceptanceRunProof
open OriginalUniverseDecoderInternalAcceptanceInductionSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalAdditionCancellationProof InternalOriginalOrderSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphChoiceProof
open InternalPositiveUnfoldingSupportProof InternalBetaTotalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open OriginalUniverseDecoder OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel
open OriginalUniverseDecoderInternalFuelIterationSyntaxProof
open OriginalUniverseDecoderInternalFuelIterationWorkProof
open OriginalUniverseDecoderInternalFuelIterationProof
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

theorem rowApply (H : Program 1) (M W : Program 2) (count second frontWork suffix joined c : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (appendRow H M W count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (SuccessfulWork H M W count frontWork c)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H M W second suffix c))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork H M W (OrdinaryArithmetic.addTerm count second) joined c)) := by
  have h := actualFiniteUniversalElimination body α 5 Gamma (appendBody H M W count)
    (fun i => emb (![second,frontWork,suffix,joined,c] i)) hrow
  rw [appendBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := OriginalLambdaConstructorGraphSyntaxProof.andIntro ha (OriginalLambdaConstructorGraphSyntaxProof.andIntro hf hs)
  exact ⟨Derivation.implicationElimination h hp⟩

theorem emptyCore (H : Program 1) (M W : Program 2) (count second frontWork suffix joined c : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn frontWork z)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H M W second suffix c))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork H M W (OrdinaryArithmetic.addTerm count second) joined c)) := by
  have hz := headTransport append joined frontWork z (Fin.cons suffix Fin.elim0) he ha
  obtain ⟨hjoined⟩ := appendZeroRecover joined suffix hz
  have hpad := successPadding H M W second count suffix c hs
  have hcount := countTransport H M W (add second count) (add count second) suffix c
    ⟨commutativity second count⟩ hpad
  exact workTransport H M W (add count second) suffix joined c ⟨symm hjoined⟩ hcount

theorem zeroCore (H : Program 1) (M W : Program 2) (second frontWork suffix joined c : OTerm α)
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (SuccessfulWork H M W z frontWork c)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H M W second suffix c))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork H M W (OrdinaryArithmetic.addTerm z second) joined c)) :=
  emptyCore H M W z second frontWork suffix joined c (zeroWork H M W frontWork c hf) ha hs

theorem zeroRow (H : Program 1) (M W : Program 2) :
    Nonempty (Derivation body Gamma (appendRow H M W z)) := by
  unfold appendRow
  apply actualFiniteUniversalIntroduction body α 5 Gamma
  let second : OTerm (α ⊕ Fin 5) := .var (.inr 0)
  let frontWork : OTerm (α ⊕ Fin 5) := .var (.inr 1)
  let suffix : OTerm (α ⊕ Fin 5) := .var (.inr 2)
  let joined : OTerm (α ⊕ Fin 5) := .var (.inr 3)
  let c : OTerm (α ⊕ Fin 5) := .var (.inr 4)
  let A := graph2 append joined frontWork suffix ⊓
    (SuccessfulWork H M W z frontWork c ⊓ SuccessfulWork H M W second suffix c)
  obtain ⟨d⟩ := zeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) H M W second frontWork suffix joined c
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  simpa only [appendBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionCoreProof
