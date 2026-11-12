module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationSuccessorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedArgumentObservations OriginalTypedArgumentObservationsTerminationSyntaxProof
open OriginalTypedArgumentObservationsInternalIterationProof OriginalTypedArgumentObservationsTerminationCoreProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] walk walkStep

theorem successorCore (R : Program 2) (count raw acc initial parameter out : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (terminalRow R count)))
 (hb : Nonempty (Derivation body Delta (InternalLessThan.strictLess raw (suc count))))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial raw acc)))
 (hr : Nonempty (Derivation body Delta (graph3 (walk R) out (suc count) initial parameter))) :
 Nonempty (Derivation body Delta (graph2 (walkStep R) out out parameter)) := by
 apply programCases InternalUnpair.left ![raw] _
 intro beta j Theta tag hj ht
 have hv : (fun i : Fin 1 => ((![raw] : Fin 1 → OTerm alpha) i).relabel j) =
     Fin.cons (raw.relabel j) Fin.elim0 := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hv] at ht
 rw [graph2Rename]
 have hrow' := renameInto hrow j Theta hj
 have hb' := renameInto hb j Theta hj
 have hp' := renameInto hp j Theta hj
 have hr' := renameInto hr j Theta hj
 rw [terminalRename] at hrow'
 simp only [InternalLessThan.strictLess,orderRename,sucRelabel] at hb'
 rw [graph2Rename] at hp'
 simp only [graph3Rename,sucRelabel] at hr'
 let E := equal tag (numeral 7)
 apply formulaCases E _
 · have he : Nonempty (Derivation body (E :: Theta) (eqn tag (numeral 7))) := by
     simpa only [E,equalEqn] using
       (show Nonempty (Derivation body (E :: Theta) E) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   have htag := outputTransport InternalUnpair.left tag (numeral 7) (Fin.cons (raw.relabel j) Fin.elim0) he (withHyp ht E)
   apply OriginalRawSyntaxTransportInternalParserBinaryProof.consCases (raw.relabel j) _ htag
   intro gamma k Xi typ child tail hk hc
   rw [graph2Rename]
   have ih := renameInto (withHyp hrow' E) k Xi hk
   have bh := renameInto (withHyp hb' E) k Xi hk
   have ph := renameInto (withHyp hp' E) k Xi hk
   have rh := renameInto (withHyp hr' E) k Xi hk
   rw [terminalRename] at ih
   simp only [InternalLessThan.strictLess,orderRename,sucRelabel] at bh
   rw [graph2Rename] at ph
   simp only [graph3Rename,sucRelabel] at rh
   exact consTerminal R ((count.relabel j).relabel k) ((raw.relabel j).relabel k)
     ((acc.relabel j).relabel k) ((initial.relabel j).relabel k) ((parameter.relabel j).relabel k)
     ((out.relabel j).relabel k) typ child tail ih bh ph rh hc
 · have hf := stoppedStep R (initial.relabel j) (raw.relabel j) (acc.relabel j) (parameter.relabel j) tag
     (withHyp hp' E.not) (withHyp ht E.not)
     (show Nonempty (Derivation body (E.not :: Theta) E.not) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   exact fixedFromRun R (suc (count.relabel j)) (initial.relabel j) (parameter.relabel j) (out.relabel j)
     hf (withHyp hr' E.not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationSuccessorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationSuccessorProof
