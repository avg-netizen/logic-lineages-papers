module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultShapeSyntax
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
open RootResultDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem fieldsSubst {beta : Type} (R : Program 2)
 (packed parameter output stack value old root tail : OTerm alpha) (ts : alpha → OTerm beta) :
 (fields R packed parameter output stack value old root tail).subst (fun a => emb (ts a)) =
 fields R (packed.subst ts) (parameter.subst ts) (output.subst ts) (stack.subst ts)
   (value.subst ts) (old.subst ts) (root.subst ts) (tail.subst ts) := by
 simp only [fields,conjunctionSubst,graph2,programSubst,consTermSubst,emptySubst,numeralSubst]
theorem fieldsRename {beta : Type} (R : Program 2)
 (packed parameter output stack value old root tail : OTerm alpha) (j : alpha → beta) :
 (fields R packed parameter output stack value old root tail).relabel j =
 fields R (packed.relabel j) (parameter.relabel j) (output.relabel j) (stack.relabel j)
   (value.relabel j) (old.relabel j) (root.relabel j) (tail.relabel j) := by
 simp only [fields,conjunctionRename,graph2Rename,numeralRename]
theorem shapeSubst {beta : Type} (R : Program 2)
 (packed parameter output : OTerm alpha) (ts : alpha → OTerm beta) :
 (Shape R packed parameter output).subst (fun a => emb (ts a)) =
 Shape R (packed.subst ts) (parameter.subst ts) (output.subst ts) := by
 unfold Shape matrix
 rw [blockSubst,liftedEmbedding]
 simp only [fieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem shapeRename {beta : Type} (R : Program 2)
 (packed parameter output : OTerm alpha) (j : alpha → beta) :
 (Shape R packed parameter output).relabel j =
 Shape R (packed.relabel j) (parameter.relabel j) (output.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (Shape R packed parameter output).subst (fun a => emb (.var (j a))) = _
 rw [shapeSubst]
 simp only [← termRelabelAsSubst]
theorem matrixWitness (R : Program 2) (packed parameter output stack value old root tail : OTerm alpha) :
 (matrix R packed parameter output).subst
   (Sum.elim Term.var (fun i => emb (![stack,value,old,root,tail] i))) =
 fields R packed parameter output stack value old root tail := by
 have he : (Sum.elim Term.var (fun i => emb (![stack,value,old,root,tail] i))) =
   (fun a => emb (Sum.elim Term.var ![stack,value,old,root,tail] a)) := by
   funext a
   cases a <;> rfl
 unfold matrix
 rw [he]
 simp only [fieldsSubst,witnessLift,Term.subst,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one,
   Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]
theorem shapeIntro (R : Program 2) (packed parameter output stack value old root tail : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields R packed parameter output stack value old root tail))) :
 Nonempty (Derivation body Delta (Shape R packed parameter output)) := by
 apply InternalFiniteBlocksProof.actualFiniteExistentialIntroduction body alpha 5 Delta
   (matrix R packed parameter output) (fun i => emb (![stack,value,old,root,tail] i))
 rw [matrixWitness]
 exact hf
theorem shapeCases (R : Program 2) (packed parameter output : OTerm alpha) (psi : Formula alpha)
 (h : Nonempty (Derivation body Delta (Shape R packed parameter output)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (stack value old root tail : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (fields R (packed.relabel j) (parameter.relabel j) (output.relabel j)
     stack value old root tail)) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 let P := matrix R packed parameter output
 apply InternalFiniteBlocksProof.actualFiniteExistentialElimination body alpha 5 Delta P psi h
 exact next (alpha ⊕ Fin 5) Sum.inl (P :: Delta.map (fun f => f.relabel Sum.inl))
   (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4))
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
   ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultShapeSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultShapeSyntax
