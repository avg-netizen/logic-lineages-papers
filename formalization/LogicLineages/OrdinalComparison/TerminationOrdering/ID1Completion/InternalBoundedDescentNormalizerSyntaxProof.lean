module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalBoundedDescentNormalizer InternalNumericIteration InternalNumericIterationSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof InternalClosedPrograms
open InternalRawListRecursionSyntaxProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof
open InternalListInduction InternalListInductionSyntaxProof
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

@[simp] theorem unaryRename {α β : Type} (p : Program 1)
    (out input : OTerm α) (j : α → β) :
    (unaryGraph p out input).relabel j = unaryGraph p (out.relabel j) (input.relabel j) := by
  simp only [unaryGraph,programRename,consTermRename,emptyRename]

@[simp] theorem unarySubst {α β : Type} (p : Program 1)
    (out input : OTerm α) (ts : α → OTerm β) :
    (unaryGraph p out input).subst (fun a => emb (ts a)) =
      unaryGraph p (out.subst ts) (input.subst ts) := by
  simp only [unaryGraph,programSubst,consTermSubst,emptySubst]

@[simp] theorem transitionRename {α β : Type} (R V : Program 1)
    (out input : OTerm α) (j : α → β) :
    (transitionGraph R V out input).relabel j =
      transitionGraph R V (out.relabel j) (input.relabel j) := by
  simp only [transitionGraph,unaryRename]

@[simp] theorem transitionSubst {α β : Type} (R V : Program 1)
    (out input : OTerm α) (ts : α → OTerm β) :
    (transitionGraph R V out input).subst (fun a => emb (ts a)) =
      transitionGraph R V (out.subst ts) (input.subst ts) := by
  simp only [transitionGraph,unarySubst]

@[simp] theorem validRename {α β : Type} (V : Program 1)
    (input : OTerm α) (j : α → β) :
    (validGraph V input).relabel j = validGraph V (input.relabel j) := by
  simp only [validGraph,unaryRename,sucRelabel,zRelabel]

@[simp] theorem validSubst {α β : Type} (V : Program 1)
    (input : OTerm α) (ts : α → OTerm β) :
    (validGraph V input).subst (fun a => emb (ts a)) = validGraph V (input.subst ts) := by
  simp only [validGraph,unarySubst,sucSubst,zSubst]

@[simp] theorem leftRename {α β : Type} (typ input : OTerm α) (j : α → β) :
    (leftGraph typ input).relabel j = leftGraph (typ.relabel j) (input.relabel j) := by
  simp only [leftGraph,unaryRename]

@[simp] theorem leftSubst {α β : Type} (typ input : OTerm α) (ts : α → OTerm β) :
    (leftGraph typ input).subst (fun a => emb (ts a)) =
      leftGraph (typ.subst ts) (input.subst ts) := by
  simp only [leftGraph,unarySubst]

@[simp] theorem atMostRename {α β : Type} (lower upper : OTerm α) (j : α → β) :
    (atMost lower upper).relabel j = atMost (lower.relabel j) (upper.relabel j) := by
  change (ltF lower (suc upper)).relabel j = ltF (lower.relabel j) (suc (upper.relabel j))
  rw [orderRename,sucRelabel]

@[simp] theorem atMostSubst {α β : Type} (lower upper : OTerm α) (ts : α → OTerm β) :
    (atMost lower upper).subst (fun a => emb (ts a)) =
      atMost (lower.subst ts) (upper.subst ts) := by
  change (ltF lower (suc upper)).subst (fun a => emb (ts a)) =
    ltF (lower.subst ts) (suc (upper.subst ts))
  rw [orderSubst,sucSubst]

/-- A single internal induction simultaneously retains the unconditional
bound, validity and tag implications, and the conditional fuel conclusion. -/
def resultFormula {α : Type} (R V : Program 1)
    (count input out typ : OTerm α) : Formula α :=
  atMost out input ⊓
    ((validGraph V input).imp (validGraph V out) ⊓
      ((leftGraph typ input).imp (leftGraph typ out) ⊓
        (atMost input count).imp (transitionGraph R V out out)))

@[simp] theorem resultSubst {α β : Type} (R V : Program 1)
    (count input out typ : OTerm α) (ts : α → OTerm β) :
    (resultFormula R V count input out typ).subst (fun a => emb (ts a)) =
      resultFormula R V (count.subst ts) (input.subst ts) (out.subst ts) (typ.subst ts) := by
  simp only [resultFormula,conjunctionSubst,impSubst,atMostSubst,validSubst,leftSubst,transitionSubst]

@[simp] theorem resultRename {α β : Type} (R V : Program 1)
    (count input out typ : OTerm α) (j : α → β) :
    (resultFormula R V count input out typ).relabel j =
      resultFormula R V (count.relabel j) (input.relabel j) (out.relabel j) (typ.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (resultFormula R V count input out typ).subst (fun a => emb (.var (j a))) = _
  rw [resultSubst]
  simp only [← termRelabelAsSubst]

/-- Inputs, output and tag are universally quantified INSIDE the invariant,
so the induction hypothesis applies to the actual next transition value. -/
def iterationBody {α : Type} (R V : Program 1) (count : OTerm α) : Formula (α ⊕ Fin 3) :=
  (repeatGraph (transition R V) (.var (.inr 1)) (count.relabel Sum.inl) (.var (.inr 0))).imp
    (resultFormula R V (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)))

def iterationRow {α : Type} (R V : Program 1) (count : OTerm α) : Formula α :=
  allBlock (iterationBody R V count)

theorem rowSubst {α β : Type} (R V : Program 1) (count : OTerm α) (ts : α → OTerm β) :
    (iterationRow R V count).subst (fun a => emb (ts a)) = iterationRow R V (count.subst ts) := by
  unfold iterationRow iterationBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [repeatSubst,resultSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem rowRename {α β : Type} (R V : Program 1) (count : OTerm α) (j : α → β) :
    (iterationRow R V count).relabel j = iterationRow R V (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (iterationRow R V count).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]

theorem bodyWitness {α : Type} (R V : Program 1) (count input out typ : OTerm α) :
    (iterationBody R V count).subst
      (Sum.elim Term.var (fun i => emb (![input,out,typ] i))) =
      (repeatGraph (transition R V) out count input).imp (resultFormula R V count input out typ) := by
  have he : (Sum.elim Term.var (fun i => emb (![input,out,typ] i))) =
      (fun a => emb (Sum.elim Term.var ![input,out,typ] a)) := by
    funext a
    cases a <;> rfl
  unfold iterationBody
  rw [he,impSubst]
  simp only [repeatSubst,resultSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rowInstantiate {α : Type} (R V : Program 1)
    (count : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (iterationRow R V count) (emb t) = iterationRow R V (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]

theorem rowSuccessor {α : Type} (R V : Program 1) (count : OTerm (α ⊕ Fin 1)) :
    successorInstance (iterationRow R V count) = iterationRow R V (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerSyntaxProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerSyntaxProof
