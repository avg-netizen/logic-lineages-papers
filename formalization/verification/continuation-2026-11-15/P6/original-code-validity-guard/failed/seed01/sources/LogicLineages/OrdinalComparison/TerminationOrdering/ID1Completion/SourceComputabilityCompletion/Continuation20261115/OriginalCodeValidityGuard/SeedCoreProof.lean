module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.SeedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.SeedCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalAcceptanceSupportProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof InternalRawListRecursionSupportProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof InternalListCodecSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open InternalOriginalOrderSyntaxProof InternalSquareRootArithmeticSupportProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open SeedSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zerosCons (count tail output : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalCodeDecoderTable.zeros tail count)))
    (ho : Nonempty (Derivation body Delta (graph1 OriginalCodeDecoderTable.zeros output (suc count)))) :
    Nonempty (Derivation body Delta (consGraph output z tail)) := by
  have h := recursionRecover .zero OriginalCodeDecoderTable.zerosStep output tail count Fin.elim0 ht ho
  let xs : Fin 2 → OTerm alpha := Fin.cons count (Fin.cons tail Fin.elim0)
  exact binaryRecover InternalListCodec.consCode (OriginalRawSyntaxTransport.constant 2 0) (.projection 1)
    output z tail xs h (constantValue 0 xs) (projectionValue 1 xs)

theorem zeroCore (output index : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields z output index))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup z index output)) := by
  obtain ⟨hb⟩ := andLeft hf
  obtain ⟨hn⟩ := InternalApplicationValidityStackAppendTransitionProof.notLessZero (body := body) (Gamma := Delta) index
  exact ⟨Derivation.explosion (Derivation.implicationElimination hn hb)⟩

theorem consCore (count tail output index : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row count)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalCodeDecoderTable.zeros tail count)))
    (hc : Nonempty (Derivation body Delta (consGraph output z tail)))
    (hb : Nonempty (Derivation body Delta (Below index (suc count)))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup z index output)) := by
  apply formulaCases (eqn index z)
  · have hl := OriginalAllPositionContextDeleteBaseProof.lookupZero output z tail (withHyp hc (eqn index z))
    exact headTransport InternalRawListRecursion.lookup z z index (Fin.cons output Fin.elim0)
      ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ hl
  · let A := (eqn index z).not
    apply InternalAcceptanceSupportProof.programCases InternalEqualityTest.predecessor (Fin.cons index Fin.elim0) _
    intro beta j Theta pred hj hp
    simp only [graph2Rename,zRelabel]
    simp only [consTermRename,emptyRename] at hp
    have hn : Nonempty (Derivation body Theta (eqn (index.relabel j) z).not) := by
      simpa only [A,InternalListCodecDecompositionSupportProof.nonzeroRename] using
        (Nonempty.intro (Derivation.hypothesis (hj A List.mem_cons_self)))
    have he := InternalListCodecDecompositionSupportProof.predecessorAtNonzero (index.relabel j) pred hn hp
    have hb' := InternalGraphCompositionFunctionalityProof.renameInto (withHyp hb A) j Theta hj
    simp only [Below,orderRename,sucRelabel] at hb'
    obtain ⟨he'⟩ := he
    obtain ⟨hb'⟩ := hb'
    have hsmall := OriginalContextInsertionBelowCoreProof.successorStrict pred (count.relabel j)
      ⟨orderLeft (suc (count.relabel j)) he' hb'⟩
    have hr' := InternalGraphCompositionFunctionalityProof.renameInto (withHyp hr A) j Theta hj
    rw [rowRename] at hr'
    have ht' := InternalGraphCompositionFunctionalityProof.renameInto (withHyp ht A) j Theta hj
    rw [graph1Rename] at ht'
    have hc' := InternalGraphCompositionFunctionalityProof.renameInto (withHyp hc A) j Theta hj
    simp only [consGraphRename,zRelabel] at hc'
    have hl := rowApply (count.relabel j) (tail.relabel j) pred hr' (andIntro hsmall ht')
    have hi := OriginalAllPositionContextDeleteDropProof.lookupConsIff
      (output.relabel j) z (tail.relabel j) pred z hc'
    have hout := OriginalTypedDecoderTransportLogicalProof.iffBackward hi hl
    exact headTransport InternalRawListRecursion.lookup z (suc pred) (index.relabel j)
      (Fin.cons (output.relabel j) Fin.elim0) ⟨symm he'⟩ hout

theorem succCore (count output index : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row count)))
    (hf : Nonempty (Derivation body Delta (fields (suc count) output index))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup z index output)) := by
  apply InternalAcceptanceSupportProof.programCases OriginalCodeDecoderTable.zeros (Fin.cons count Fin.elim0) _
  intro beta j Theta tail hj ht
  simp only [graph2Rename,zRelabel]
  simp only [consTermRename,emptyRename] at ht
  have hr' := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [rowRename] at hr'
  have hf' := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  simp only [fieldsRename,sucRelabel] at hf'
  have hc := zerosCons (count.relabel j) tail (output.relabel j) ht (andRight hf')
  exact consCore (count.relabel j) tail (output.relabel j) (index.relabel j) hr' ht hc (andLeft hf')
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.SeedCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.SeedCoreProof
