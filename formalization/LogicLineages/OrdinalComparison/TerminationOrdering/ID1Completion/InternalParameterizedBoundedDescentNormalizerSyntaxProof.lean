module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationLawsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedBoundedDescentNormalizer InternalParameterizedNumericIteration
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

@[simp] theorem binaryRename {α β : Type} (p : Program 2)
    (out input parameter : OTerm α) (j : α → β) :
    (binaryGraph p out input parameter).relabel j =
      binaryGraph p (out.relabel j) (input.relabel j) (parameter.relabel j) := by
  simp only [binaryGraph,programRename,consTermRename,emptyRename]

@[simp] theorem binarySubst {α β : Type} (p : Program 2)
    (out input parameter : OTerm α) (ts : α → OTerm β) :
    (binaryGraph p out input parameter).subst (fun a => emb (ts a)) =
      binaryGraph p (out.subst ts) (input.subst ts) (parameter.subst ts) := by
  simp only [binaryGraph,programSubst,consTermSubst,emptySubst]

@[simp] theorem transitionRename {α β : Type} (R V : Program 2)
    (out input parameter : OTerm α) (j : α → β) :
    (transitionGraph R V out input parameter).relabel j =
      transitionGraph R V (out.relabel j) (input.relabel j) (parameter.relabel j) := by
  simp only [transitionGraph,binaryRename]

@[simp] theorem transitionSubst {α β : Type} (R V : Program 2)
    (out input parameter : OTerm α) (ts : α → OTerm β) :
    (transitionGraph R V out input parameter).subst (fun a => emb (ts a)) =
      transitionGraph R V (out.subst ts) (input.subst ts) (parameter.subst ts) := by
  simp only [transitionGraph,binarySubst]

@[simp] theorem validRename {α β : Type} (V : Program 2)
    (input parameter : OTerm α) (j : α → β) :
    (validGraph V input parameter).relabel j =
      validGraph V (input.relabel j) (parameter.relabel j) := by
  simp only [validGraph,binaryRename,sucRelabel,zRelabel]

@[simp] theorem validSubst {α β : Type} (V : Program 2)
    (input parameter : OTerm α) (ts : α → OTerm β) :
    (validGraph V input parameter).subst (fun a => emb (ts a)) =
      validGraph V (input.subst ts) (parameter.subst ts) := by
  simp only [validGraph,binarySubst,sucSubst,zSubst]

@[simp] theorem leftRename {α β : Type} (typ input : OTerm α) (j : α → β) :
    (leftGraph typ input).relabel j = leftGraph (typ.relabel j) (input.relabel j) := by
  simp only [leftGraph,programRename,consTermRename,emptyRename]

@[simp] theorem leftSubst {α β : Type} (typ input : OTerm α) (ts : α → OTerm β) :
    (leftGraph typ input).subst (fun a => emb (ts a)) =
      leftGraph (typ.subst ts) (input.subst ts) := by
  simp only [leftGraph,programSubst,consTermSubst,emptySubst]

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

/-- Substitution for the actual parameter-carrying repeat AST, without
specializing the arbitrary binary program at a metalanguage parameter. -/
@[simp] theorem repeatSubst {α β : Type} (P : Program 2)
    (out count input parameter : OTerm α) (ts : α → OTerm β) :
    (repeatGraph P out count input parameter).subst (fun a => emb (ts a)) =
      repeatGraph P (out.subst ts) (count.subst ts) (input.subst ts) (parameter.subst ts) := by
  simp only [repeatGraph,programSubst,consTermSubst,emptySubst]

/-- One internal invariant retains the unconditional value bound, validity
at the unchanged parameter, the original value tag, and the fuel conclusion. -/
def resultFormula {α : Type} (R V : Program 2)
    (count input out typ parameter : OTerm α) : Formula α :=
  atMost out input ⊓
    ((validGraph V input parameter).imp (validGraph V out parameter) ⊓
      ((leftGraph typ input).imp (leftGraph typ out) ⊓
        (atMost input count).imp (transitionGraph R V out out parameter)))

@[simp] theorem resultSubst {α β : Type} (R V : Program 2)
    (count input out typ parameter : OTerm α) (ts : α → OTerm β) :
    (resultFormula R V count input out typ parameter).subst (fun a => emb (ts a)) =
      resultFormula R V (count.subst ts) (input.subst ts) (out.subst ts)
        (typ.subst ts) (parameter.subst ts) := by
  simp only [resultFormula,conjunctionSubst,impSubst,atMostSubst,validSubst,leftSubst,transitionSubst]

@[simp] theorem resultRename {α β : Type} (R V : Program 2)
    (count input out typ parameter : OTerm α) (j : α → β) :
    (resultFormula R V count input out typ parameter).relabel j =
      resultFormula R V (count.relabel j) (input.relabel j) (out.relabel j)
        (typ.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (resultFormula R V count input out typ parameter).subst (fun a => emb (.var (j a))) = _
  rw [resultSubst]
  simp only [← termRelabelAsSubst]

/-- All four terms [input,out,typ,parameter] are universally quantified
INSIDE the invariant, so internal induction can vary the next value while
retaining the identical runtime parameter. -/
def iterationBody {α : Type} (R V : Program 2) (count : OTerm α) : Formula (α ⊕ Fin 4) :=
  (repeatGraph (transition R V) (.var (.inr 1)) (count.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 3))).imp
    (resultFormula R V (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
      (.var (.inr 2)) (.var (.inr 3)))

def iterationRow {α : Type} (R V : Program 2) (count : OTerm α) : Formula α :=
  allBlock (iterationBody R V count)

theorem rowSubst {α β : Type} (R V : Program 2) (count : OTerm α) (ts : α → OTerm β) :
    (iterationRow R V count).subst (fun a => emb (ts a)) = iterationRow R V (count.subst ts) := by
  unfold iterationRow iterationBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [repeatSubst,resultSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem rowRename {α β : Type} (R V : Program 2) (count : OTerm α) (j : α → β) :
    (iterationRow R V count).relabel j = iterationRow R V (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (iterationRow R V count).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]

theorem bodyWitness {α : Type} (R V : Program 2)
    (count input out typ parameter : OTerm α) :
    (iterationBody R V count).subst
      (Sum.elim Term.var (fun i => emb (![input,out,typ,parameter] i))) =
      (repeatGraph (transition R V) out count input parameter).imp
        (resultFormula R V count input out typ parameter) := by
  have he : (Sum.elim Term.var (fun i => emb (![input,out,typ,parameter] i))) =
      (fun a => emb (Sum.elim Term.var ![input,out,typ,parameter] a)) := by
    funext a
    cases a <;> rfl
  unfold iterationBody
  rw [he,impSubst]
  simp only [repeatSubst,resultSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rowInstantiate {α : Type} (R V : Program 2)
    (count : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (iterationRow R V count) (emb t) = iterationRow R V (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]

theorem rowSuccessor {α : Type} (R V : Program 2) (count : OTerm (α ⊕ Fin 1)) :
    successorInstance (iterationRow R V count) = iterationRow R V (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerSyntaxProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerSyntaxProof
