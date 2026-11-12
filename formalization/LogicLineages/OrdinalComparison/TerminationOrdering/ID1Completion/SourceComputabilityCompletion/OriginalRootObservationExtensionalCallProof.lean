module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceAgreementProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalCallProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalRecursionClosureSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalClosedPrograms InternalClosedProgramsBindingProof InternalFiniteBlocksSubstitutionProof
open InternalTagArithmeticSyntaxProof (emb bindEmbedding varBind)
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open OriginalTypedArgumentObservationsCongruence OriginalTypedArgumentObservationsCongruenceSyntaxProof
open OriginalTypedArgumentObservationsAccumulatorQueryProof OriginalTypedArgumentObservationsCongruenceAgreementProof
open OriginalRootObservationExtensional
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem globalSubst {beta : Type} (R S : Program 2) (ts : alpha → OrdinaryArithmetic.Term beta) :
 (GlobalAgreement R S : Formula alpha).subst (fun a => emb (ts a)) = (GlobalAgreement R S : Formula beta) := by
 unfold GlobalAgreement
 rw [allBlockSubst,liftedEmbedding,agreementSubst]
 rfl

theorem globalRename {beta : Type} (R S : Program 2) (rho : alpha → beta) :
 (GlobalAgreement R S : Formula alpha).relabel rho = (GlobalAgreement R S : Formula beta) := by
 rw [formulaRelabelAsSubst]
 change (GlobalAgreement R S : Formula alpha).subst (fun a => emb (.var (rho a))) = _
 exact globalSubst R S (fun a => .var (rho a))

theorem globalAt (R S : Program 2) (parameter : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (GlobalAgreement R S))) :
 Nonempty (Derivation body Delta (Agreement R S parameter)) := by
 have h := actualFiniteUniversalElimination body alpha 1 Delta
   (Agreement R S (.var (.inr (0 : Fin 1)))) (fun _ => emb parameter) hg
 change Nonempty (Derivation body Delta (instantiate (Agreement R S (.var (.inr (0 : Fin 1)))) (emb parameter))) at h
 simpa only [instantiate,bindEmbedding,agreementSubst,varBind] using h

theorem outerCallForward (R S A B : Program 2) (parameter input out : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (GlobalAgreement R S)))
 (ho : Nonempty (Derivation body Delta (graph2 (.composition R ![A,B]) out input parameter))) :
 Nonempty (Derivation body Delta (graph2 (.composition S ![A,B]) out input parameter)) := by
 apply binaryCases A input parameter _
 intro beta rho Theta a hrho ha
 rw [graph2Rename]
 have hg' := renameInto hg rho Theta hrho
 rw [globalRename] at hg'
 have ho' := renameInto ho rho Theta hrho
 rw [graph2Rename] at ho'
 apply binaryCases B (input.relabel rho) (parameter.relabel rho) _
 intro gamma j Xi b hj hb
 rw [graph2Rename]
 have hg'' := renameInto hg' j Xi hj
 rw [globalRename] at hg''
 have ho'' := renameInto ho' j Xi hj
 have ha' := renameInto ha j Xi hj
 rw [graph2Rename] at ho'' ha'
 let xs : Fin 2 → OTerm gamma := ![(input.relabel rho).relabel j,(parameter.relabel rho).relabel j]
 have hr := binaryRecover R A B ((out.relabel rho).relabel j) (a.relabel j) b xs ho'' ha' hb
 have hs := agreementForward R S b (a.relabel j) ((out.relabel rho).relabel j) (globalAt R S b hg'') hr
 exact binaryValue S A B ((out.relabel rho).relabel j) (a.relabel j) b xs hs ha' hb

theorem outerCallAgreement (R S A B : Program 2) (parameter : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (GlobalAgreement R S))) :
 Nonempty (Derivation body Delta (Agreement (.composition R ![A,B]) (.composition S ![A,B]) parameter)) := by
 apply agreementIntro _ _ parameter
 intro beta rho Theta input left right hrho hl hr
 have hg' := renameInto hg rho Theta hrho
 rw [globalRename] at hg'
 have hs := outerCallForward R S A B (parameter.relabel rho) input left hg' hl
 simpa only [equalEqn] using valueUnique (.composition S ![A,B]) left right ![input,parameter.relabel rho] hs hr

theorem fixedCallForward (R S A : Program 2) (parameter input out : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (Agreement R S parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 (.composition R ![A,.projection 1]) out input parameter))) :
 Nonempty (Derivation body Delta (graph2 (.composition S ![A,.projection 1]) out input parameter)) := by
 apply binaryCases A input parameter _
 intro beta rho Theta a hrho ha
 rw [graph2Rename]
 have hg' := renameInto hg rho Theta hrho
 rw [agreementRename] at hg'
 have ho' := renameInto ho rho Theta hrho
 rw [graph2Rename] at ho'
 let xs : Fin 2 → OTerm beta := ![input.relabel rho,parameter.relabel rho]
 have hr := binaryRecover R A (.projection 1) (out.relabel rho) a (parameter.relabel rho) xs ho' ha (projectionValue 1 xs)
 have hs := agreementForward R S (parameter.relabel rho) a (out.relabel rho) hg' hr
 exact binaryValue S A (.projection 1) (out.relabel rho) a (parameter.relabel rho) xs hs ha (projectionValue 1 xs)

theorem fixedCallAgreement (R S A : Program 2) (parameter : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (Agreement R S parameter))) :
 Nonempty (Derivation body Delta (Agreement (.composition R ![A,.projection 1]) (.composition S ![A,.projection 1]) parameter)) := by
 apply agreementIntro _ _ parameter
 intro beta rho Theta input left right hrho hl hr
 have hg' := renameInto hg rho Theta hrho
 rw [agreementRename] at hg'
 have hs := fixedCallForward R S A (parameter.relabel rho) input left hg' hl
 simpa only [equalEqn] using valueUnique (.composition S ![A,.projection 1]) left right ![input,parameter.relabel rho] hs hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalCallProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalCallProof
