module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalScanSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalTransparentMinimum InternalGraphComposition
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof InternalClosedPrograms
open InternalRawListRecursionSyntaxProof InternalOriginalOrderSyntaxProof
open InternalQuotientComparisonSyntaxProof InternalListInduction InternalListInductionSyntaxProof
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

@[simp] theorem graphRename {α β : Type} (Q : Program 3)
    (out x y z : OTerm α) (j : α → β) :
    (graph3 Q out x y z).relabel j =
      graph3 Q (out.relabel j) (x.relabel j) (y.relabel j) (z.relabel j) := by
  simp only [graph3,programRename,consTermRename,emptyRename]

@[simp] theorem graphSubst {α β : Type} (Q : Program 3)
    (out x y z : OTerm α) (ts : α → OTerm β) :
    (graph3 Q out x y z).subst (fun a => emb (ts a)) =
      graph3 Q (out.subst ts) (x.subst ts) (y.subst ts) (z.subst ts) := by
  simp only [graph3,programSubst,consTermSubst,emptySubst]

/-- Internal induction invariant. The exact-bound absence clause follows
from the third conjunct by equality transport. No evaluated predicate occurs. -/
def resultFormula {α : Type} (Q : Program 3)
    (bound seed parameter out earlier : OTerm α) : Formula α :=
  ltF out (suc bound) ⊓
    (((ltF out bound).imp (graph3 Q (suc z) seed out parameter)) ⊓
      ((ltF earlier out).imp (graph3 Q (suc z) seed earlier parameter).not))

@[simp] theorem resultSubst {α β : Type} (Q : Program 3)
    (bound seed parameter out earlier : OTerm α) (ts : α → OTerm β) :
    (resultFormula Q bound seed parameter out earlier).subst (fun a => emb (ts a)) =
      resultFormula Q (bound.subst ts) (seed.subst ts) (parameter.subst ts)
        (out.subst ts) (earlier.subst ts) := by
  simp only [resultFormula,conjunctionSubst,impSubst,orderSubst,graphSubst,sucSubst,zSubst,notSubst]

@[simp] theorem resultRename {α β : Type} (Q : Program 3)
    (bound seed parameter out earlier : OTerm α) (j : α → β) :
    (resultFormula Q bound seed parameter out earlier).relabel j =
      resultFormula Q (bound.relabel j) (seed.relabel j) (parameter.relabel j)
        (out.relabel j) (earlier.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (resultFormula Q bound seed parameter out earlier).subst (fun a => emb (.var (j a))) = _
  rw [resultSubst]
  simp only [← termRelabelAsSubst]

theorem resultInstantiate {α : Type} (Q : Program 3)
    (bound seed parameter out earlier : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (resultFormula Q bound seed parameter out earlier) (emb t) =
      resultFormula Q (bound.subst (bindTerm t)) (seed.subst (bindTerm t))
        (parameter.subst (bindTerm t)) (out.subst (bindTerm t)) (earlier.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,resultSubst]

def scanBody {α : Type} (Q : Program 3) (bound : OTerm α) : Formula (α ⊕ Fin 4) :=
  (graph3 (scan Q) (.var (.inr 2)) (bound.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))).imp
    (resultFormula Q (bound.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
      (.var (.inr 2)) (.var (.inr 3)))

def scanRow {α : Type} (Q : Program 3) (bound : OTerm α) : Formula α := allBlock (scanBody Q bound)

theorem rowSubst {α β : Type} (Q : Program 3) (bound : OTerm α) (ts : α → OTerm β) :
    (scanRow Q bound).subst (fun a => emb (ts a)) = scanRow Q (bound.subst ts) := by
  unfold scanRow scanBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [graphSubst,resultSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem rowRename {α β : Type} (Q : Program 3) (bound : OTerm α) (j : α → β) :
    (scanRow Q bound).relabel j = scanRow Q (bound.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (scanRow Q bound).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]

theorem bodyWitness {α : Type} (Q : Program 3) (bound seed parameter out earlier : OTerm α) :
    (scanBody Q bound).subst (Sum.elim Term.var (fun i => emb (![seed,parameter,out,earlier] i))) =
      (graph3 (scan Q) out bound seed parameter).imp (resultFormula Q bound seed parameter out earlier) := by
  have he : (Sum.elim Term.var (fun i => emb (![seed,parameter,out,earlier] i))) =
      (fun a => emb (Sum.elim Term.var ![seed,parameter,out,earlier] a)) := by
    funext a
    cases a <;> rfl
  unfold scanBody
  rw [he,impSubst]
  simp only [graphSubst,resultSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rowInstantiate {α : Type} (Q : Program 3) (bound : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (scanRow Q bound) (emb t) = scanRow Q (bound.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]

theorem rowSuccessor {α : Type} (Q : Program 3) (bound : OTerm (α ⊕ Fin 1)) :
    successorInstance (scanRow Q bound) = scanRow Q (bound.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalScanSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalScanSyntaxProof
