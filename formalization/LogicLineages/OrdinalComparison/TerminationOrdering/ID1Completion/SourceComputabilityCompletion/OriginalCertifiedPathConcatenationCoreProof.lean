module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsWalkQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalGraphCompositionEqualityProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open OriginalCertifiedPathConcatenationDefinitions OriginalCertifiedPathConcatenationSyntaxProof OriginalCertifiedPathConcatenationBindingProof
open OriginalTypedArgumentObservationsWalkQueryProof OriginalTypedArgumentObservationsAccumulatorQueryProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {edge : Program 3} {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rawTransport (source target raw other : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn raw other)))
 (hp : Nonempty (Derivation body Delta (InternalPathChecker.pathGraph edge source target raw))) :
 Nonempty (Derivation body Delta (InternalPathChecker.pathGraph edge source target other)) := by
 apply graphInputTransport body alpha 3 Delta _ (suc z)
   (Fin.cons source (Fin.cons target (Fin.cons raw Fin.elim0)))
   (Fin.cons source (Fin.cons target (Fin.cons other Fin.elim0))) _ hp
 intro i
 refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) i
 · rw [onEquality]; exact ⟨InternalTagArithmeticSupportProof.refl source⟩
 · rw [onEquality]; exact ⟨InternalTagArithmeticSupportProof.refl target⟩
 · rw [onEquality]; exact he

theorem atZero (raw source middle target right combined : OTerm alpha)
 (hz : Nonempty (Derivation body Delta (eqn raw z)))
 (hf : Nonempty (Derivation body Delta (fields edge raw source middle target right combined))) :
 Nonempty (Derivation body Delta (result edge source target combined)) := by
 obtain ⟨he⟩ := InternalPathCheckerProof.nilRecover edge source middle (rawTransport source middle raw z hz (andLeft hf))
 have hs : Nonempty (Derivation body Delta (InternalPathChecker.pathGraph edge source target right)) :=
   headTransport (InternalPathChecker.checker edge false) (suc z) middle source (Fin.cons target (Fin.cons right Fin.elim0))
     ⟨InternalTagArithmeticSupportProof.symm (by simpa only [equalEqn] using he)⟩ (andLeft (andRight hf))
 have ha := headTransport InternalApplicationValidityStackAppend.append combined raw z (Fin.cons right Fin.elim0) hz (andRight (andRight hf))
 obtain ⟨hc⟩ := InternalApplicationValidityStackAppendListProof.appendZeroRecover combined right ha
 exact rawTransport source target right combined ⟨InternalTagArithmeticSupportProof.symm hc⟩ hs

theorem atCons (raw source middle target right combined entry rest : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw edge raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw entry rest)))
 (hf : Nonempty (Derivation body Delta (fields edge raw source middle target right combined))) :
 Nonempty (Derivation body Delta (result edge source target combined)) := by
 apply pairCases entry _
 intro beta j Theta vertex certificate hj hp
 rw [resultRename]
 have hi' := renameInto hi j Theta hj
 rw [belowRawRename] at hi'
 have hc' := renameInto hc j Theta hj
 rw [graph2Rename] at hc'
 have hf' := renameInto hf j Theta hj
 simp only [fields,InternalPathChecker.pathGraph,InternalPathChecker.checkerGraph,InternalPathChecker.triple,
   conjunctionRename,graph2Rename,programRename,consTermRename,emptyRename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hf'
 apply binaryCases InternalApplicationValidityStackAppend.append (rest.relabel j) (right.relabel j) _
 intro gamma k Xi appended hk happ
 rw [resultRename]
 have hi'' := renameInto hi' k Xi hk
 rw [belowRawRename] at hi''
 have hc'' := renameInto hc' k Xi hk
 rw [graph2Rename] at hc''
 have hp' := renameInto hp k Xi hk
 rw [graph2Rename] at hp'
 have hf'' := renameInto hf' k Xi hk
 simp only [conjunctionRename,graph2Rename,programRename,consTermRename,emptyRename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hf''
 have oldParts := iffForward (InternalPathCheckerProof.pathCons edge ((source.relabel j).relabel k) ((middle.relabel j).relabel k)
   ((raw.relabel j).relabel k) ((entry.relabel j).relabel k) ((rest.relabel j).relabel k) (vertex.relabel k) (certificate.relabel k) hp' hc'') (andLeft hf'')
 have htail := belowRawApply ((raw.relabel j).relabel k) ((rest.relabel j).relabel k) (vertex.relabel k)
   ((middle.relabel j).relabel k) ((target.relabel j).relabel k) ((right.relabel j).relabel k) appended hi''
   (InternalListCodecDecompositionSupportProof.consTailDescent ((raw.relabel j).relabel k) ((entry.relabel j).relabel k) ((rest.relabel j).relabel k) hc'')
   (andIntro (andRight oldParts) (andIntro (andLeft (andRight hf'')) happ))
 have hcons := InternalApplicationValidityStackAppendListProof.consForward ((raw.relabel j).relabel k) ((entry.relabel j).relabel k)
   ((rest.relabel j).relabel k) ((right.relabel j).relabel k) appended ((combined.relabel j).relabel k) hc'' happ (andRight (andRight hf''))
 exact iffBackward (InternalPathCheckerProof.pathCons edge ((source.relabel j).relabel k) ((target.relabel j).relabel k)
   ((combined.relabel j).relabel k) ((entry.relabel j).relabel k) appended (vertex.relabel k) (certificate.relabel k) hp' hcons)
   (andIntro (andLeft oldParts) htail)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationCoreProof
