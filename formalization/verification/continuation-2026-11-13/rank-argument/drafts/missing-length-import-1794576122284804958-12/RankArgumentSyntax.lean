module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListEntryInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentSyntax
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
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (termAcceptedSubst)
open OriginalContextInsertionSyntaxProof (lengthSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open RankArgumentDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem smallSubst {beta : Type} (observations bound : OTerm alpha) (ts : alpha → OTerm beta) :
 (AllSmall observations bound).subst (fun a => emb (ts a)) =
 AllSmall (observations.subst ts) (bound.subst ts) := by
 unfold AllSmall smallMatrix
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [conjunctionSubst,lengthSubst,OriginalContextInsertion.Below,InternalLessThan.strictLess,
   orderSubst,graph2,programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
theorem smallRename {beta : Type} (observations bound : OTerm alpha) (j : alpha → beta) :
 (AllSmall observations bound).relabel j = AllSmall (observations.relabel j) (bound.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (AllSmall observations bound).subst (fun a => emb (.var (j a))) = _
 rw [smallSubst]
 simp only [← termRelabelAsSubst]
theorem weightsSubst {beta : Type} {k : Nat} (Q : Program 2) (F : Program (k+1))
 (H : Program 1) (M W : Program 2) (parameter gamma c bound : OTerm alpha) (params : Fin k → OTerm alpha)
 (ts : alpha → OTerm beta) :
 (LocalWeights Q F H M W parameter gamma c bound params).subst (fun a => emb (ts a)) =
 LocalWeights Q F H M W (parameter.subst ts) (gamma.subst ts) (c.subst ts) (bound.subst ts)
   (fun i => (params i).subst ts) := by
 unfold LocalWeights weightMatrix
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [conjunctionSubst,termAcceptedSubst,InternalLessThan.strictLess,orderSubst,
   graph1,graph2,programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
theorem weightsRename {beta : Type} {k : Nat} (Q : Program 2) (F : Program (k+1))
 (H : Program 1) (M W : Program 2) (parameter gamma c bound : OTerm alpha) (params : Fin k → OTerm alpha)
 (j : alpha → beta) :
 (LocalWeights Q F H M W parameter gamma c bound params).relabel j =
 LocalWeights Q F H M W (parameter.relabel j) (gamma.relabel j) (c.relabel j) (bound.relabel j)
   (fun i => (params i).relabel j) := by
 rw [formulaRelabelAsSubst]
 change (LocalWeights Q F H M W parameter gamma c bound params).subst (fun a => emb (.var (j a))) = _
 rw [weightsSubst]
 simp only [← termRelabelAsSubst]
theorem smallWitness (observations bound count index typed typ child : OTerm alpha) :
 (smallMatrix observations bound).subst (Sum.elim Term.var (fun i => emb (![count,index,typed,typ,child] i))) =
 (OriginalContextInsertion.lengthGraph count observations ⊓
  (OriginalContextInsertion.Below index count ⊓
  (graph2 InternalRawListRecursion.lookup typed index observations ⊓
   graph2 InternalPairing.pairing typed typ child))).imp
 (InternalLessThan.strictLess child bound) := by
 have he : (Sum.elim Term.var (fun i => emb (![count,index,typed,typ,child] i))) =
   (fun a => emb (Sum.elim Term.var ![count,index,typed,typ,child] a)) := by funext a; cases a <;> rfl
 unfold smallMatrix
 rw [he,impSubst]
 simp only [conjunctionSubst,lengthSubst,OriginalContextInsertion.Below,InternalLessThan.strictLess,
   orderSubst,graph2,programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl
theorem weightsWitness {k : Nat} (Q : Program 2) (F : Program (k+1))
 (H : Program 1) (M W : Program 2) (parameter gamma c bound : OTerm alpha) (params : Fin k → OTerm alpha)
 (typ raw packed child typed rank : OTerm alpha) :
 (weightMatrix Q F H M W parameter gamma c bound params).subst
   (Sum.elim Term.var (fun i => emb (![typ,raw,packed,child,typed,rank] i))) =
 (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W
    typ raw gamma c ⊓
  (graph2 InternalPairing.pairing packed typ raw ⊓
  (graph2 Q child packed parameter ⊓
  (graph2 InternalPairing.pairing typed typ child ⊓
  (graph1 OriginalRawSyntaxTransport.variableRankRaw rank raw ⊓
   InternalLessThan.strictLess child bound))))).imp
 (programGraph F rank (Fin.cons typed params)) := by
 have he : (Sum.elim Term.var (fun i => emb (![typ,raw,packed,child,typed,rank] i))) =
   (fun a => emb (Sum.elim Term.var ![typ,raw,packed,child,typed,rank] a)) := by funext a; cases a <;> rfl
 unfold weightMatrix
 rw [he,impSubst]
 simp only [conjunctionSubst,termAcceptedSubst,InternalLessThan.strictLess,orderSubst,
   graph1,graph2,programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentSyntax
