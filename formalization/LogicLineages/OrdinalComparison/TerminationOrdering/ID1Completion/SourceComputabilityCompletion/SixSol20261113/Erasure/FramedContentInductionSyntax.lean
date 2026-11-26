module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentInductionSyntax
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb)
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open InternalQuotientComparisonSyntaxProof (orderSubst)
open OriginalHereditaryInternalAgendaSyntaxProof (jobSubst)
open FramedContentSyntax (allContentSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open FramedContentInductionDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem belowSubst {beta : Type} (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B bound : OTerm alpha) (ts : alpha → OTerm beta) :
 (BelowContent R H M W c B bound).subst (fun a => emb (ts a)) =
 BelowContent R H M W (c.subst ts) (B.subst ts) (bound.subst ts) := by
 unfold BelowContent belowMatrix
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [conjunctionSubst,jobSubst,allContentSubst,InternalOriginalOrderSyntaxProof.ltF,orderSubst,
   graph1,programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
theorem belowRename {beta : Type} (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B bound : OTerm alpha) (j : alpha → beta) :
 (BelowContent R H M W c B bound).relabel j =
 BelowContent R H M W (c.relabel j) (B.relabel j) (bound.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (BelowContent R H M W c B bound).subst (fun a => emb (.var (j a))) = _
 rw [belowSubst]
 simp only [← termRelabelAsSubst]
theorem belowWitness (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B bound job weight : OTerm alpha) :
 (belowMatrix R H M W c B bound).subst (Sum.elim Term.var (fun i => emb (![job,weight] i))) =
 (OriginalHereditaryInternalAgenda.Job H M W c B job ⊓
  (graph1 OriginalHereditaryFuelProgram.weight weight job ⊓ InternalOriginalOrderSyntaxProof.ltF weight bound)).imp
  (FramedContentDefinitions.AllFramedContent R job) := by
 have he : (Sum.elim Term.var (fun i => emb (![job,weight] i))) =
   (fun a => emb (Sum.elim Term.var ![job,weight] a)) := by funext a; cases a <;> rfl
 unfold belowMatrix
 rw [he,impSubst]
 simp only [conjunctionSubst,jobSubst,allContentSubst,InternalOriginalOrderSyntaxProof.ltF,orderSubst,
   graph1,programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr,
   Matrix.cons_val_zero,Matrix.cons_val_one]
theorem belowApply (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B bound job weight : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (BelowContent R H M W c B bound)))
 (hj : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight job)))
 (hlt : Nonempty (Derivation body Delta (InternalOriginalOrderSyntaxProof.ltF weight bound))) :
 Nonempty (Derivation body Delta (FramedContentDefinitions.AllFramedContent R job)) := by
 have h := actualFiniteUniversalElimination body alpha 2 Delta (belowMatrix R H M W c B bound)
   (fun i => emb (![job,weight] i)) hb
 rw [belowWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hj⟩ := hj
 obtain ⟨hw⟩ := hw
 obtain ⟨hlt⟩ := hlt
 exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction hj (Derivation.conjunctionIntroduction hw hlt))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentInductionSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentInductionSyntax
