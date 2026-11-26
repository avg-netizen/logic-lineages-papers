module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanRowSyntax
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
open InternalAdditionLawsProof (impSubst add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ExpansionMapGeometryScanDefinitions
open Runtime
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open InternalQuotientComparisonSyntaxProof (orderSubst)
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open ExpansionMapGeometryScanSyntax
open InternalTagArithmeticSyntaxProof (bindTerm bindEmbedding nextTerm nextEmbedding)
def rowBody (count start role typ raw jobs prefixRow : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
 (graph5 OriginalHereditaryAnnotatedExpansion.scan (.var (.inr 0))
   (add (start.relabel Sum.inl) (count.relabel Sum.inl))
   (role.relabel Sum.inl) (typ.relabel Sum.inl) (raw.relabel Sum.inl) (jobs.relabel Sum.inl)).imp
 (Extension (count.relabel Sum.inl) (prefixRow.relabel Sum.inl) (.var (.inr 0)))
def row (count start role typ raw jobs prefixRow : OTerm alpha) : Formula alpha :=
 allBlock (rowBody count start role typ raw jobs prefixRow)
theorem rowSubst {beta : Type} (count start role typ raw jobs prefixRow : OTerm alpha) (ts : alpha → OTerm beta) :
 (row count start role typ raw jobs prefixRow).subst (fun a => emb (ts a)) =
 row (count.subst ts) (start.subst ts) (role.subst ts) (typ.subst ts) (raw.subst ts) (jobs.subst ts) (prefixRow.subst ts) := by
 unfold row rowBody
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [extensionSubst,graph5,programSubst,consTermSubst,emptySubst,InternalAdditionLawsProof.addSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (count start role typ raw jobs prefixRow : OTerm alpha) (j : alpha → beta) :
 (row count start role typ raw jobs prefixRow).relabel j =
 row (count.relabel j) (start.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j) (jobs.relabel j) (prefixRow.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (row count start role typ raw jobs prefixRow).subst (fun a => emb (.var (j a))) = _
 rw [rowSubst]
 simp only [← termRelabelAsSubst]
theorem rowWitness (count start role typ raw jobs prefixRow full : OTerm alpha) :
 (rowBody count start role typ raw jobs prefixRow).subst (Sum.elim Term.var (fun _ : Fin 1 => emb full)) =
 (graph5 OriginalHereditaryAnnotatedExpansion.scan full (add start count) role typ raw jobs).imp
 (Extension count prefixRow full) := by
 have he : (Sum.elim Term.var (fun _ : Fin 1 => emb full)) =
   (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => full) a)) := by funext a; cases a <;> rfl
 unfold rowBody
 rw [he,impSubst]
 simp only [extensionSubst,graph5,programSubst,consTermSubst,emptySubst,InternalAdditionLawsProof.addSubst,witnessLift,Term.subst,Sum.elim_inr]
theorem rowApply (count start role typ raw jobs prefixRow full : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row count start role typ raw jobs prefixRow)))
 (hf : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan full (add start count) role typ raw jobs))) :
 Nonempty (Derivation body Delta (Extension count prefixRow full)) := by
 have h := actualFiniteUniversalElimination body alpha 1 Delta
   (rowBody count start role typ raw jobs prefixRow) (fun _ => emb full) hi
 rw [rowWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanRowSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanRowSyntax
