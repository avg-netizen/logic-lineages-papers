module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanSyntax
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb)
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst numeralSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ExpansionMapGeometryScanDefinitions
open Runtime
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open PrefixFrameSyntax (frameSubst frameRename)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open InternalQuotientComparisonSyntaxProof (orderSubst)
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
theorem extensionSubst {beta : Type} (count prefixRow full : OTerm alpha) (ts : alpha → OTerm beta) :
 (Extension count prefixRow full).subst (fun a => emb (ts a)) =
 Extension (count.subst ts) (prefixRow.subst ts) (full.subst ts) := by
 unfold Extension suffixMatrix
 rw [blockSubst,liftedEmbedding]
 simp only [conjunctionSubst,lengthSubst,graph2,programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
theorem extensionRename {beta : Type} (count prefixRow full : OTerm alpha) (j : alpha → beta) :
 (Extension count prefixRow full).relabel j = Extension (count.relabel j) (prefixRow.relabel j) (full.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (Extension count prefixRow full).subst (fun a => emb (.var (j a))) = _
 rw [extensionSubst]
 simp only [← termRelabelAsSubst]
theorem extensionWitness (count prefixRow full suffix : OTerm alpha) :
 (suffixMatrix count prefixRow full).subst (Sum.elim Term.var (fun _ : Fin 1 => emb suffix)) =
 (lengthGraph count suffix ⊓ graph2 InternalApplicationValidityStackAppend.append full prefixRow suffix) := by
 have he : (Sum.elim Term.var (fun _ : Fin 1 => emb suffix)) =
   (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => suffix) a)) := by funext a; cases a <;> rfl
 unfold suffixMatrix
 rw [he]
 simp only [conjunctionSubst,lengthSubst,graph2,programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
theorem extensionIntro (count prefixRow full suffix : OTerm alpha)
 (h : Nonempty (Derivation body Delta
   (lengthGraph count suffix ⊓ graph2 InternalApplicationValidityStackAppend.append full prefixRow suffix))) :
 Nonempty (Derivation body Delta (Extension count prefixRow full)) := by
 apply InternalFiniteBlocksProof.actualFiniteExistentialIntroduction body alpha 1 Delta
   (suffixMatrix count prefixRow full) (fun _ => emb suffix)
 rw [extensionWitness]
 exact h
theorem extensionCases (count prefixRow full : OTerm alpha) (psi : Formula alpha)
 (h : Nonempty (Derivation body Delta (Extension count prefixRow full)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (suffix : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (lengthGraph (count.relabel j) suffix ⊓
     graph2 InternalApplicationValidityStackAppend.append (full.relabel j) (prefixRow.relabel j) suffix)) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 let P := suffixMatrix count prefixRow full
 apply InternalFiniteBlocksProof.actualFiniteExistentialElimination body alpha 1 Delta P psi h
 exact next (alpha ⊕ Fin 1) Sum.inl (P :: Delta.map (fun f => f.relabel Sum.inl))
   (.var (.inr 0)) (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
   ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanSyntax
