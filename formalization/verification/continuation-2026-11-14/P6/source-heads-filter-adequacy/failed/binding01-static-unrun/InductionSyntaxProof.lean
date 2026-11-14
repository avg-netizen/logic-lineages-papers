module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.InductionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Induction
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
open InternalStrongInduction

theorem implicationRename {alpha beta : Type} (p q : Formula alpha) (j : alpha → beta) :
    (p.imp q).relabel j = (p.relabel j).imp (q.relabel j) := rfl
theorem notRename {alpha beta : Type} (p : Formula alpha) (j : alpha → beta) :
    p.not.relabel j = (p.relabel j).not := rfl

@[simp] theorem resultRename {alpha beta : Type}
    (raw reached candidate parameter out value : OTerm alpha) (j : alpha → beta) :
    (result raw reached candidate parameter out value).relabel j =
      result (raw.relabel j) (reached.relabel j) (candidate.relabel j) (parameter.relabel j) (out.relabel j) (value.relabel j) := by
  simp only [result,qualifies,implicationRename,notRename,eqnRelabel,conjunctionRename,graph2,graph3,programRename,consTermRename,emptyRename,numeral,sucRelabel,zRelabel]

theorem atRawSubst (n : Nat) (arity : Fin n → Nat) {alpha beta : Type} 
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw n arity raw).subst (fun a => emb (ts a)) = AtRaw n arity (raw.subst ts) := by
  unfold AtRaw matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,notSubst,equalSubst,fields,result,qualifies,eqnSubst,graph2,graph3,graph3,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename (n : Nat) (arity : Fin n → Nat) {alpha beta : Type} 
    (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw n arity raw).relabel j = AtRaw n arity (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw n arity raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (n : Nat) (arity : Fin n → Nat) {alpha : Type} (input reached candidate parameter out value : OTerm alpha) :
    (matrix n arity input).subst (Sum.elim Term.var (fun i => emb (![reached,candidate,parameter,out,value] i))) =
      (fields n arity input reached candidate parameter out value).imp (result input reached candidate parameter out value) := by
  have he : (Sum.elim Term.var (fun i => emb (![reached,candidate,parameter,out,value] i))) =
      (fun a => emb (Sum.elim Term.var ![reached,candidate,parameter,out,value] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix fields
  rw [he]
  simp only [impSubst,conjunctionSubst,notSubst,result,qualifies,eqnSubst,graph2,graph3,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rawPredicateInstantiate (n : Nat) (arity : Fin n → Nat) {alpha : Type}  (raw : OTerm alpha) :
    instantiate (rawPredicate n arity) (emb raw) = AtRaw n arity raw := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

@[simp] theorem belowRawRename (n : Nat) (arity : Fin n → Nat) {alpha beta : Type} 
    (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw n arity raw).relabel j = BelowRaw n arity (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl

theorem rawPredicateLift (n : Nat) (arity : Fin n → Nat) {alpha : Type}  :
    lift (rawPredicate n arity (alpha := alpha)) = rawPredicate n arity (alpha := alpha ⊕ Fin 1) := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.InductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.InductionSyntaxProof
