module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionSplitSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionSplitCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructorsSupportProof
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

open OriginalUniverseDecoderInternalAcceptanceInductionSplitSyntaxProof

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

theorem splitRowApply (H : Program 1) (M W : Program 2) (count frontWork suffix joined c : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (splitRow H M W count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H M W count joined c))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork H M W count frontWork c ⊓ SuccessfulWork H M W count suffix c)) := by
  have h := actualFiniteUniversalElimination body α 4 Gamma (splitBody H M W count)
    (fun i => emb (![frontWork,suffix,joined,c] i)) hrow
  rw [splitBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := OriginalLambdaConstructorGraphSyntaxProof.andIntro ha hs
  exact ⟨Derivation.implicationElimination h hp⟩

theorem splitEmptyCore (H : Program 1) (M W : Program 2) (count frontWork suffix joined c : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn frontWork z)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H M W count joined c))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork H M W count frontWork c ⊓ SuccessfulWork H M W count suffix c)) := by
  have hz := headTransport append joined frontWork z (Fin.cons suffix Fin.elim0) he ha
  have hj := appendZeroRecover joined suffix hz
  obtain ⟨he⟩ := he
  exact OriginalLambdaConstructorGraphSyntaxProof.andIntro (workTransport H M W count z frontWork c ⟨symm he⟩ (nilSuccess H M W count c))
    (workTransport H M W count joined suffix c hj hs)

theorem splitZeroCore (H : Program 1) (M W : Program 2) (frontWork suffix joined c : OTerm α)
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H M W z joined c))) :
    Nonempty (Derivation body Gamma
      (SuccessfulWork H M W z frontWork c ⊓ SuccessfulWork H M W z suffix c)) := by
  apply formulaCases (eqn frontWork z)
  · exact splitEmptyCore H M W z frontWork suffix joined c
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha _) (withHyp hs _)
  · obtain ⟨hn⟩ := appendNonzero frontWork suffix joined (withHyp ha _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hz⟩ := zeroWork H M W joined c (withHyp hs _)
    exact ⟨Derivation.explosion (Derivation.implicationElimination hn hz)⟩

theorem splitZeroRow (H : Program 1) (M W : Program 2) :
    Nonempty (Derivation body Gamma (splitRow H M W z)) := by
  unfold splitRow
  apply actualFiniteUniversalIntroduction body α 4 Gamma
  let frontWork : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let suffix : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let joined : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let c : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  let A := graph2 append joined frontWork suffix ⊓ SuccessfulWork H M W z joined c
  obtain ⟨d⟩ := splitZeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) H M W frontWork suffix joined c
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [splitBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionSplitCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionSplitCoreProof
