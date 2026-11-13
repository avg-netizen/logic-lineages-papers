module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseTagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentSourceTagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsWalkQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSourceCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open OriginalTypedDecoderInternalBranchProof (orCases)
open OriginalHereditaryValidityInternalNodeSupportProof (weakenProof)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem packedTags (H G : Program 1) (M W : Program 2) (input parameter tag : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag tag input))) :
 Nonempty (Derivation body Delta (equal tag (numeral 0) ⊔ (equal tag (numeral 1) ⊔
   (equal tag (numeral 2) ⊔ (equal tag (numeral 3) ⊔ (equal tag (numeral 4) ⊔ equal tag (numeral 5))))))) := by
 apply OriginalTypedArgumentObservationsWalkQueryProof.pairCases input _
 intro beta j Theta typ raw hj hp
 have hs' := renameInto hs j Theta hj
 have ht' := renameInto ht j Theta hj
 simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hs' ht'
 have h := Context.EvaluatorAlignmentSourceTagsProof.sourceTags H G M W (input.relabel j) (parameter.relabel j) (tag.relabel j)
   hs' (RankCalibrationBaseTagProof.liftTag (input.relabel j) (parameter.relabel j) typ raw (tag.relabel j) hp ht')
 simpa only [OriginalUniverseDecoderInternalBooleanProof.orRename,OriginalTypedDecoderInternalLogicSyntaxProof.equalRename,
   GuardedSourceSyntaxProof.numeralRename] using h

theorem sixCases (tag : OTerm alpha) (psi : Formula alpha)
 (h : Nonempty (Derivation body Delta (equal tag (numeral 0) ⊔ (equal tag (numeral 1) ⊔
   (equal tag (numeral 2) ⊔ (equal tag (numeral 3) ⊔ (equal tag (numeral 4) ⊔ equal tag (numeral 5))))))))
 (next : ∀ (i : Fin 6) (Theta : List (Formula alpha)),
   (∀ q ∈ Delta, q ∈ Theta) → Nonempty (Derivation body Theta (equal tag (numeral i.val))) →
   Nonempty (Derivation body Theta psi)) : Nonempty (Derivation body Delta psi) := by
 let A0 := equal tag (numeral 0)
 let A1 := equal tag (numeral 1)
 let A2 := equal tag (numeral 2)
 let A3 := equal tag (numeral 3)
 let A4 := equal tag (numeral 4)
 let A5 := equal tag (numeral 5)
 let B4 := A4 ⊔ A5
 let B3 := A3 ⊔ B4
 let B2 := A2 ⊔ B3
 let B1 := A1 ⊔ B2
 apply orCases h
 ·
   exact next 0 _ (fun q hq => List.mem_cons_of_mem _ (hq)) ⟨Derivation.hypothesis List.mem_cons_self⟩
 ·
   apply orCases (show Nonempty (Derivation body (B1 :: Delta) B1) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   ·
     exact next 1 _ (fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hq))) ⟨Derivation.hypothesis List.mem_cons_self⟩
   ·
     apply orCases (show Nonempty (Derivation body (B2 :: B1 :: Delta) B2) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
     ·
       exact next 2 _ (fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hq)))) ⟨Derivation.hypothesis List.mem_cons_self⟩
     ·
       apply orCases (show Nonempty (Derivation body (B3 :: B2 :: B1 :: Delta) B3) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
       ·
         exact next 3 _ (fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hq))))) ⟨Derivation.hypothesis List.mem_cons_self⟩
       ·
         apply orCases (show Nonempty (Derivation body (B4 :: B3 :: B2 :: B1 :: Delta) B4) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
         ·
           exact next 4 _ (fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hq)))))) ⟨Derivation.hypothesis List.mem_cons_self⟩
         ·
           exact next 5 _ (fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hq)))))) ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem actualCases (H G : Program 1) (M W : Program 2) (input parameter : OTerm alpha) (psi : Formula alpha)
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (i : Fin 6),
   (∀ q ∈ Delta, q.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph1 OriginalLambdaConstructor.tag (numeral i.val) (input.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 apply programCases OriginalLambdaConstructor.tag (Fin.cons input Fin.elim0) psi
 intro beta j Theta tag hj ht
 simp only [consTermRename,emptyRename] at ht
 have hs' := renameInto hs j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hs'
 apply sixCases tag _ (packedTags H G M W (input.relabel j) (parameter.relabel j) tag hs' ht)
 intro i Xi inc he
 simp only [equalEqn] at he
 have htag := outputTransport OriginalLambdaConstructor.tag tag (numeral i.val)
   (Fin.cons (input.relabel j) Fin.elim0) he (weakenProof ht inc)
 exact next beta j Xi i (fun q hq => inc _ (hj q hq)) htag
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSourceCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSourceCasesProof
