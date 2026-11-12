module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorConsCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorFixedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationSuccessorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorSuccessorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (suc sucRelabel eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalTypedArgumentObservations OriginalTypedArgumentObservationsAccumulatorSyntaxProof
open OriginalTypedArgumentObservationsInternalIterationProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] walk walkStep

theorem successorCore (R : Program 2)
 (count raw acc1 acc2 suffix initial1 initial2 parameter out1 out2 remaining1 remaining2 result1 result2 : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (accumulatorRow R count)))
 (hp1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial1 raw acc1)))
 (hp2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial2 raw acc2)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append acc2 acc1 suffix)))
 (hr1 : Nonempty (Derivation body Delta (graph3 (walk R) out1 (suc count) initial1 parameter)))
 (hr2 : Nonempty (Derivation body Delta (graph3 (walk R) out2 (suc count) initial2 parameter)))
 (hout1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out1 remaining1 result1)))
 (hout2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out2 remaining2 result2)))
 : Nonempty (Derivation body Delta (equal remaining1 remaining2 ⊓
   graph2 InternalApplicationValidityStackAppend.append result2 result1 suffix)) := by
 apply programCases InternalUnpair.left (Fin.cons raw Fin.elim0) _
 intro beta j Theta tag hj ht
 have hv : (fun i : Fin 1 => ((Fin.cons raw Fin.elim0 : Fin 1 → OTerm alpha) i).relabel j) = Fin.cons (raw.relabel j) Fin.elim0 := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hv] at ht
 simp only [conjunctionRename,equalRename,graph2Rename]
 have hrow' := renameInto hrow j Theta hj
 simp only [accumulatorRename] at hrow'
 have hp1' := renameInto hp1 j Theta hj
 simp only [graph2Rename,graph3Rename,sucRelabel] at hp1'
 have hp2' := renameInto hp2 j Theta hj
 simp only [graph2Rename,graph3Rename,sucRelabel] at hp2'
 have ha' := renameInto ha j Theta hj
 simp only [graph2Rename,graph3Rename,sucRelabel] at ha'
 have hr1' := renameInto hr1 j Theta hj
 simp only [graph2Rename,graph3Rename,sucRelabel] at hr1'
 have hr2' := renameInto hr2 j Theta hj
 simp only [graph2Rename,graph3Rename,sucRelabel] at hr2'
 have hout1' := renameInto hout1 j Theta hj
 simp only [graph2Rename,graph3Rename,sucRelabel] at hout1'
 have hout2' := renameInto hout2 j Theta hj
 simp only [graph2Rename,graph3Rename,sucRelabel] at hout2'
 let E := equal tag (numeral 7)
 apply formulaCases E _
 · have he : Nonempty (Derivation body (E :: Theta) (eqn tag (numeral 7))) := by
     simpa only [E,equalEqn] using
       (show Nonempty (Derivation body (E :: Theta) E) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   have htag := outputTransport InternalUnpair.left tag (numeral 7) (Fin.cons (raw.relabel j) Fin.elim0) he (withHyp ht E)
   apply OriginalRawSyntaxTransportInternalParserBinaryProof.consCases (raw.relabel j) _ htag
   intro gamma k Xi typ child tail hk hc
   simp only [conjunctionRename,equalRename,graph2Rename]
   have hrow'' := renameInto (withHyp hrow' E) k Xi hk
   simp only [accumulatorRename] at hrow''
   have hp1'' := renameInto (withHyp hp1' E) k Xi hk
   simp only [graph2Rename,graph3Rename,sucRelabel] at hp1''
   have hp2'' := renameInto (withHyp hp2' E) k Xi hk
   simp only [graph2Rename,graph3Rename,sucRelabel] at hp2''
   have ha'' := renameInto (withHyp ha' E) k Xi hk
   simp only [graph2Rename,graph3Rename,sucRelabel] at ha''
   have hr1'' := renameInto (withHyp hr1' E) k Xi hk
   simp only [graph2Rename,graph3Rename,sucRelabel] at hr1''
   have hr2'' := renameInto (withHyp hr2' E) k Xi hk
   simp only [graph2Rename,graph3Rename,sucRelabel] at hr2''
   have hout1'' := renameInto (withHyp hout1' E) k Xi hk
   simp only [graph2Rename,graph3Rename,sucRelabel] at hout1''
   have hout2'' := renameInto (withHyp hout2' E) k Xi hk
   simp only [graph2Rename,graph3Rename,sucRelabel] at hout2''
   exact OriginalTypedArgumentObservationsAccumulatorConsCoreProof.consSuccessor R
     ((count.relabel j).relabel k) ((raw.relabel j).relabel k) ((acc1.relabel j).relabel k) ((acc2.relabel j).relabel k) ((suffix.relabel j).relabel k) ((initial1.relabel j).relabel k) ((initial2.relabel j).relabel k) ((parameter.relabel j).relabel k) ((out1.relabel j).relabel k) ((out2.relabel j).relabel k) ((remaining1.relabel j).relabel k) ((remaining2.relabel j).relabel k) ((result1.relabel j).relabel k) ((result2.relabel j).relabel k) typ child tail
     hrow'' hp1'' hp2'' ha'' hr1'' hr2'' hout1'' hout2'' hc
 · have hfixed1 := stoppedIteration R (suc (count.relabel j)) (initial1.relabel j) (raw.relabel j) (acc1.relabel j) (parameter.relabel j) tag
     (withHyp hp1' E.not) (withHyp ht E.not)
     (show Nonempty (Derivation body (E.not :: Theta) E.not) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   have hfixed2 := stoppedIteration R (suc (count.relabel j)) (initial2.relabel j) (raw.relabel j) (acc2.relabel j) (parameter.relabel j) tag
     (withHyp hp2' E.not) (withHyp ht E.not)
     (show Nonempty (Derivation body (E.not :: Theta) E.not) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   exact OriginalTypedArgumentObservationsAccumulatorFixedProof.fixedSuffix R
     (suc (count.relabel j)) (raw.relabel j) (acc1.relabel j) (acc2.relabel j) (suffix.relabel j) (initial1.relabel j) (initial2.relabel j) (parameter.relabel j) (out1.relabel j) (out2.relabel j) (remaining1.relabel j) (remaining2.relabel j) (result1.relabel j) (result2.relabel j)
     (withHyp hp1' E.not) (withHyp hp2' E.not) (withHyp ha' E.not) hfixed1 hfixed2
     (withHyp hr1' E.not) (withHyp hr2' E.not) (withHyp hout1' E.not) (withHyp hout2' E.not)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorSuccessorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorSuccessorProof
