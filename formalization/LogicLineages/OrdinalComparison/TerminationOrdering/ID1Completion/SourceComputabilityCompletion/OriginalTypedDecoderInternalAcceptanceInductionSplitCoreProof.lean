module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionSplitSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionSplitCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructorsSupportProof
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

open OriginalTypedDecoderInternalAcceptanceInductionSplitSyntaxProof

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

def listQueries : Fin 3 → Program 2 := ![
  .composition InternalListCodec.headCode (fun _ : Fin 1 => .projection 0),
  .composition InternalListCodec.tailCode (fun _ : Fin 1 => .projection 0),
  .composition append (Fin.cons
    (.composition InternalListCodec.tailCode (fun _ : Fin 1 => .projection 0))
    (Fin.cons (.projection 1) Fin.elim0))]

theorem appendNonzero (frontWork suffix joined : OTerm α)
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hn : Nonempty (Derivation body Gamma (eqn frontWork z).not)) :
    Nonempty (Derivation body Gamma (eqn joined z).not) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases listQueries (Fin.cons frontWork (Fin.cons suffix Fin.elim0)) _
  intro β j ys Delta hj hq
  rw [InternalListCodecDecompositionSupportProof.nonzeroRename]
  simp only [consTermRename,emptyRename] at hq
  let xs : Fin 2 → OTerm β := Fin.cons (frontWork.relabel j) (Fin.cons (suffix.relabel j) Fin.elim0)
  have hh := unaryRecover InternalListCodec.headCode (.projection 0)
    (ys 0) (frontWork.relabel j) xs (hq 0) (projectionValue 0 xs)
  have ht := unaryRecover InternalListCodec.tailCode (.projection 0)
    (ys 1) (frontWork.relabel j) xs (hq 1) (projectionValue 0 xs)
  have hjt := binaryRecover append
    (.composition InternalListCodec.tailCode (fun _ : Fin 1 => .projection 0)) (.projection 1)
    (ys 2) (ys 1) (suffix.relabel j) xs (hq 2) (hq 1) (projectionValue 1 xs)
  have hn' := renameInto hn j Delta hj
  rw [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn'
  have ha' := renameInto ha j Delta hj
  rw [graph2Rename] at ha'
  have hc := InternalListCodecDecompositionSupportProof.reconstructNonzero
    (frontWork.relabel j) (ys 0) (ys 1) hn' hh ht
  have hjc := consForward (frontWork.relabel j) (ys 0) (ys 1) (suffix.relabel j)
    (ys 2) (joined.relabel j) hc hjt ha'
  exact OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight (InternalListCodecSupportProof.consDestruction
    (joined.relabel j) (ys 0) (ys 2) hjc))

theorem splitRowApply (H : Program 1) (count frontWork suffix joined : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (splitRow H count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H count joined))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork H count frontWork ⊓ SuccessfulWork H count suffix)) := by
  have h := actualFiniteUniversalElimination body α 3 Gamma (splitBody H count)
    (fun i => emb (![frontWork,suffix,joined] i)) hrow
  rw [splitBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := OriginalLambdaConstructorGraphSyntaxProof.andIntro ha hs
  exact ⟨Derivation.implicationElimination h hp⟩

theorem splitEmptyCore (H : Program 1) (count frontWork suffix joined : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn frontWork z)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H count joined))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork H count frontWork ⊓ SuccessfulWork H count suffix)) := by
  have hz := headTransport append joined frontWork z (Fin.cons suffix Fin.elim0) he ha
  have hj := appendZeroRecover joined suffix hz
  obtain ⟨he⟩ := he
  exact OriginalLambdaConstructorGraphSyntaxProof.andIntro (workTransport H count z frontWork ⟨symm he⟩ (nilSuccess H count))
    (workTransport H count joined suffix hj hs)

theorem splitZeroCore (H : Program 1) (frontWork suffix joined : OTerm α)
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H z joined))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork H z frontWork ⊓ SuccessfulWork H z suffix)) := by
  apply formulaCases (eqn frontWork z)
  · exact splitEmptyCore H z frontWork suffix joined
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha _) (withHyp hs _)
  · obtain ⟨hn⟩ := appendNonzero frontWork suffix joined (withHyp ha _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hz⟩ := zeroWork H joined (withHyp hs _)
    exact ⟨Derivation.explosion (Derivation.implicationElimination hn hz)⟩

theorem splitZeroRow (H : Program 1) :
    Nonempty (Derivation body Gamma (splitRow H z)) := by
  unfold splitRow
  apply actualFiniteUniversalIntroduction body α 3 Gamma
  let frontWork : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let suffix : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let joined : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let A := graph2 append joined frontWork suffix ⊓ SuccessfulWork H z joined
  obtain ⟨d⟩ := splitZeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) H frontWork suffix joined
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [splitBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionSplitCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionSplitCoreProof
