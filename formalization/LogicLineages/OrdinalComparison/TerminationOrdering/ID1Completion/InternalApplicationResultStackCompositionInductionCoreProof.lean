module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionInductionCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationResultStackComposition InternalApplicationCertificateConstructors
open InternalApplicationValidityStackAppend (append)
open InternalApplicationResultStackCompositionSyntaxProof InternalApplicationResultStackCompositionStateProof
open InternalApplicationResultStackCompositionRunProof InternalApplicationResultStackCompositionBasicProof
open InternalApplicationResultStackCompositionInductionSyntaxProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationValidityStackAppendListProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalApplicationStepPeelSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalAdditionCancellationProof InternalOriginalOrderSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem workRowApply (guard leaf : Program 1) (combine : Program 4)
    (count second frontWork suffix joined initialResults middleResults finalResults : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (workRow guard leaf combine count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma
      (actualRun guard leaf combine count frontWork initialResults middleResults)))
    (hs : Nonempty (Derivation body Gamma
      (actualRun guard leaf combine second suffix middleResults finalResults))) :
    Nonempty (Derivation body Gamma
      (actualRun guard leaf combine (add count second) joined initialResults finalResults)) := by
  have h := actualFiniteUniversalElimination body α 7 Gamma (workBody guard leaf combine count)
    (fun i => emb (![second,frontWork,suffix,joined,initialResults,middleResults,finalResults] i)) hrow
  rw [workBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := andIntro ha (andIntro hf hs)
  exact ⟨Derivation.implicationElimination h hp⟩

theorem resultRowApply (guard leaf : Program 1) (combine : Program 4)
    (count work initialResults finalResults background framedInitial framedFinal : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (resultRow guard leaf combine count)))
    (hr : Nonempty (Derivation body Gamma (actualRun guard leaf combine count work initialResults finalResults)))
    (hi : Nonempty (Derivation body Gamma (graph2 append framedInitial initialResults background)))
    (hf : Nonempty (Derivation body Gamma (graph2 append framedFinal finalResults background))) :
    Nonempty (Derivation body Gamma (actualRun guard leaf combine count work framedInitial framedFinal)) := by
  have h := actualFiniteUniversalElimination body α 6 Gamma (resultBody guard leaf combine count)
    (fun i => emb (![work,initialResults,finalResults,background,framedInitial,framedFinal] i)) hrow
  rw [resultBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := andIntro hr (andIntro hi hf)
  exact ⟨Derivation.implicationElimination h hp⟩

theorem workEmptyCore (guard leaf : Program 1) (combine : Program 4)
    (count second frontWork suffix joined initialResults middleResults finalResults : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn frontWork z)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma
      (actualRun guard leaf combine count frontWork initialResults middleResults)))
    (hs : Nonempty (Derivation body Gamma
      (actualRun guard leaf combine second suffix middleResults finalResults))) :
    Nonempty (Derivation body Gamma
      (actualRun guard leaf combine (add count second) joined initialResults finalResults)) := by
  have hz := headTransport append joined frontWork z (Fin.cons suffix Fin.elim0) he ha
  obtain ⟨hjoined⟩ := appendZeroRecover joined suffix hz
  have hresults := emptyRunResults guard leaf combine count frontWork initialResults middleResults he hf
  have hstart := initialResultsTransport guard leaf combine second suffix middleResults initialResults finalResults hresults hs
  have hpad := runPadding guard leaf combine second count suffix initialResults finalResults hstart
  have hcount := countTransport guard leaf combine (add second count) (add count second)
    suffix initialResults finalResults ⟨commutativity second count⟩ hpad
  exact workTransport guard leaf combine (add count second) suffix joined initialResults finalResults
    ⟨symm hjoined⟩ hcount

theorem workZeroCore (guard leaf : Program 1) (combine : Program 4)
    (second frontWork suffix joined initialResults middleResults finalResults : OTerm α)
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (actualRun guard leaf combine z frontWork initialResults middleResults)))
    (hs : Nonempty (Derivation body Gamma (actualRun guard leaf combine second suffix middleResults finalResults))) :
    Nonempty (Derivation body Gamma
      (actualRun guard leaf combine (add z second) joined initialResults finalResults)) :=
  workEmptyCore guard leaf combine z second frontWork suffix joined initialResults middleResults finalResults
    (andLeft (zeroRunRecover guard leaf combine frontWork initialResults middleResults hf)) ha hf hs

theorem resultZeroCore (guard leaf : Program 1) (combine : Program 4)
    (work initialResults finalResults background framedInitial framedFinal : OTerm α)
    (hr : Nonempty (Derivation body Gamma (actualRun guard leaf combine z work initialResults finalResults)))
    (hi : Nonempty (Derivation body Gamma (graph2 append framedInitial initialResults background)))
    (hf : Nonempty (Derivation body Gamma (graph2 append framedFinal finalResults background))) :
    Nonempty (Derivation body Gamma (actualRun guard leaf combine z work framedInitial framedFinal)) := by
  have hzero := zeroRunRecover guard leaf combine work initialResults finalResults hr
  have hf' := headTransport append framedFinal finalResults initialResults
    (Fin.cons background Fin.elim0) (andRight hzero) hf
  have heq := valueUnique append framedFinal framedInitial
    (Fin.cons initialResults (Fin.cons background Fin.elim0)) hf' hi
  exact zeroRunIntro guard leaf combine work framedInitial framedFinal (andLeft hzero) heq

theorem workZeroRow (guard leaf : Program 1) (combine : Program 4) :
    Nonempty (Derivation body Gamma (workRow guard leaf combine z)) := by
  unfold workRow
  apply actualFiniteUniversalIntroduction body α 7 Gamma
  let second : OTerm (α ⊕ Fin 7) := .var (.inr 0)
  let frontWork : OTerm (α ⊕ Fin 7) := .var (.inr 1)
  let suffix : OTerm (α ⊕ Fin 7) := .var (.inr 2)
  let joined : OTerm (α ⊕ Fin 7) := .var (.inr 3)
  let initialResults : OTerm (α ⊕ Fin 7) := .var (.inr 4)
  let middleResults : OTerm (α ⊕ Fin 7) := .var (.inr 5)
  let finalResults : OTerm (α ⊕ Fin 7) := .var (.inr 6)
  let A := graph2 append joined frontWork suffix ⊓
    (actualRun guard leaf combine z frontWork initialResults middleResults ⊓
      actualRun guard leaf combine second suffix middleResults finalResults)
  obtain ⟨d⟩ := workZeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) guard leaf combine
    second frontWork suffix joined initialResults middleResults finalResults
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  simpa only [workBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem resultZeroRow (guard leaf : Program 1) (combine : Program 4) :
    Nonempty (Derivation body Gamma (resultRow guard leaf combine z)) := by
  unfold resultRow
  apply actualFiniteUniversalIntroduction body α 6 Gamma
  let work : OTerm (α ⊕ Fin 6) := .var (.inr 0)
  let initialResults : OTerm (α ⊕ Fin 6) := .var (.inr 1)
  let finalResults : OTerm (α ⊕ Fin 6) := .var (.inr 2)
  let background : OTerm (α ⊕ Fin 6) := .var (.inr 3)
  let framedInitial : OTerm (α ⊕ Fin 6) := .var (.inr 4)
  let framedFinal : OTerm (α ⊕ Fin 6) := .var (.inr 5)
  let A := actualRun guard leaf combine z work initialResults finalResults ⊓
    (graph2 append framedInitial initialResults background ⊓ graph2 append framedFinal finalResults background)
  obtain ⟨d⟩ := resultZeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) guard leaf combine
    work initialResults finalResults background framedInitial framedFinal
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  simpa only [resultBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionInductionCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionInductionCoreProof
