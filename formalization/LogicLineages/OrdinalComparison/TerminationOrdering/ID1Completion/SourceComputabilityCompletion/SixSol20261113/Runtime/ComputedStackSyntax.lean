module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackSyntax
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalFiniteBlocks InternalFiniteBlocksBindingProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalSourceIntroductionSyntaxProof
open InternalTagArithmeticSyntaxProof (emb)
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open OriginalTypedDecoderInternalLogicSyntaxProof (numeralSubst)
open GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open ComputedStackDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem fieldsSubst {beta : Type} (R : Program 2)
 (packed parameter output stack value : OTerm alpha) (ts : alpha → OTerm beta) :
 (fields R packed parameter output stack value).subst (fun a => emb (ts a)) =
 fields R (packed.subst ts) (parameter.subst ts) (output.subst ts) (stack.subst ts)
   (value.subst ts)  := by
 simp only [fields,conjunctionSubst,graph2,programSubst,consTermSubst,emptySubst,numeralSubst]
theorem fieldsRename {beta : Type} (R : Program 2)
 (packed parameter output stack value : OTerm alpha) (j : alpha → beta) :
 (fields R packed parameter output stack value).relabel j =
 fields R (packed.relabel j) (parameter.relabel j) (output.relabel j) (stack.relabel j)
   (value.relabel j)  := by
 simp only [fields,conjunctionRename,graph2Rename,numeralRename]
theorem shapeSubst {beta : Type} (R : Program 2)
 (packed parameter output : OTerm alpha) (ts : alpha → OTerm beta) :
 (SingletonResult R packed parameter output).subst (fun a => emb (ts a)) =
 SingletonResult R (packed.subst ts) (parameter.subst ts) (output.subst ts) := by
 unfold SingletonResult matrix
 rw [OriginalContextInsertionSyntaxProof.blockSubst,liftedEmbedding]
 simp only [fieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem shapeRename {beta : Type} (R : Program 2)
 (packed parameter output : OTerm alpha) (j : alpha → beta) :
 (SingletonResult R packed parameter output).relabel j =
 SingletonResult R (packed.relabel j) (parameter.relabel j) (output.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (SingletonResult R packed parameter output).subst (fun a => emb (.var (j a))) = _
 rw [shapeSubst]
 simp only [← termRelabelAsSubst]
theorem matrixWitness (R : Program 2) (packed parameter output stack value : OTerm alpha) :
 (matrix R packed parameter output).subst
   (Sum.elim Term.var (fun i => emb (![stack,value] i))) =
 fields R packed parameter output stack value := by
 have he : (Sum.elim Term.var (fun i => emb (![stack,value] i))) =
   (fun a => emb (Sum.elim Term.var ![stack,value] a)) := by
   funext a
   cases a <;> rfl
 unfold matrix
 rw [he]
 simp only [fieldsSubst,witnessLift,Term.subst,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one,
   Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]
theorem shapeIntro (R : Program 2) (packed parameter output stack value : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields R packed parameter output stack value))) :
 Nonempty (Derivation body Delta (SingletonResult R packed parameter output)) := by
 apply InternalFiniteBlocksProof.actualFiniteExistentialIntroduction body alpha 2 Delta
   (matrix R packed parameter output) (fun i => emb (![stack,value] i))
 rw [matrixWitness]
 exact hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackSyntax
