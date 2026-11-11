module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationValidityStackAppend InternalApplicationCertificateConstructors
open InternalApplicationValidityStackAppendSyntaxProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationValidityStackAppendListProof OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendRunProof
open OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalAdditionCancellationProof InternalOriginalOrderSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphChoiceProof
open InternalPositiveUnfoldingSupportProof InternalBetaTotalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceIterationWorkProof
open OriginalHereditaryValidityInternalRecurrenceIterationProof
open OriginalHereditaryValidityInternalRecurrenceIterationTerminalProof (successPair)
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

theorem rowApply (s t m : Program 2) (count second frontWork suffix joined : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (appendRow s t m count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (SuccessfulWork s t m count frontWork)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork s t m second suffix))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork s t m (OrdinaryArithmetic.addTerm count second) joined)) := by
  have h := actualFiniteUniversalElimination body α 4 Gamma (appendBody s t m count)
    (fun i => emb (![second,frontWork,suffix,joined] i)) hrow
  rw [appendBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := OriginalLambdaConstructorGraphSyntaxProof.andIntro ha (OriginalLambdaConstructorGraphSyntaxProof.andIntro hf hs)
  exact ⟨Derivation.implicationElimination h hp⟩

theorem emptyCore (s t m : Program 2) (count second frontWork suffix joined : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn frontWork z)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork s t m second suffix))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork s t m (OrdinaryArithmetic.addTerm count second) joined)) := by
  have hz := headTransport append joined frontWork z (Fin.cons suffix Fin.elim0) he ha
  obtain ⟨hjoined⟩ := appendZeroRecover joined suffix hz
  have hpad := successPadding s t m second count suffix hs
  have hcount := countTransport s t m (add second count) (add count second) suffix
    ⟨commutativity second count⟩ hpad
  exact workTransport s t m (add count second) suffix joined ⟨symm hjoined⟩ hcount

theorem zeroCore (s t m : Program 2) (second frontWork suffix joined : OTerm α)
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (SuccessfulWork s t m z frontWork)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork s t m second suffix))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork s t m (OrdinaryArithmetic.addTerm z second) joined)) :=
  emptyCore s t m z second frontWork suffix joined (zeroWork s t m frontWork hf) ha hs

theorem zeroRow (s t m : Program 2) :
    Nonempty (Derivation body Gamma (appendRow s t m z)) := by
  unfold appendRow
  apply actualFiniteUniversalIntroduction body α 4 Gamma
  let second : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let frontWork : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let suffix : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let joined : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  let A := graph2 append joined frontWork suffix ⊓
    (SuccessfulWork s t m z frontWork ⊓ SuccessfulWork s t m second suffix)
  obtain ⟨d⟩ := zeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) s t m second frontWork suffix joined
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  simpa only [appendBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionCoreProof
