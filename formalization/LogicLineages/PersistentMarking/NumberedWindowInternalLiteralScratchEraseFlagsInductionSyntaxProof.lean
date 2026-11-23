module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseFlagsInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseFlagsInductionSyntaxProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof (orSubst)
open InternalAdditionLawsProof (impSubst)
open InternalStrongInduction
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalLiteralScratchEraseFlagsConsProof (flags)
open NumberedWindowInternalLiteralScratchEraseFlagsInductionDefinitions

theorem flagsSubst {alpha beta : Type} (raw needle bit : OTerm alpha) (ts : alpha → OTerm beta) :
    (flags raw needle bit).subst (fun a => emb (ts a)) =
      flags (raw.subst ts) (needle.subst ts) (bit.subst ts) := by
  have ht : (fun (i : Fin 2) => (![raw,needle] i).subst ts) =
      (![raw.subst ts,needle.subst ts] : Fin 2 → OTerm beta) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t)) i
  unfold flags memberGraph
  simp only [impSubst,conjunctionSubst,orSubst,eqnSubst,programSubst,zSubst,sucSubst,ht]

theorem flagsRename {alpha beta : Type} (raw needle bit : OTerm alpha) (j : alpha → beta) :
    (flags raw needle bit).relabel j = flags (raw.relabel j) (needle.relabel j) (bit.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (flags raw needle bit).subst (fun a => emb (.var (j a))) = _
  rw [flagsSubst]
  simp only [← termRelabelAsSubst]

theorem atRawSubst {alpha beta : Type} (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw raw).subst (fun a => emb (ts a)) = AtRaw (raw.subst ts) := by
  unfold AtRaw matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,fields,flagsSubst,graph2,programSubst,consTermSubst,
    emptySubst,InternalRecursionGraphSyntaxProof.liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename {alpha beta : Type} (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw raw).relabel j = AtRaw (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

private theorem fieldsSubst {alpha beta : Type} (raw needle acc bit rest : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (fields raw needle acc bit rest).subst (fun a => emb (ts a)) =
      fields (raw.subst ts) (needle.subst ts) (acc.subst ts) (bit.subst ts) (rest.subst ts) := by
  unfold fields
  simp only [conjunctionSubst,graph2,programSubst,consTermSubst,emptySubst]

theorem matrixWitness {alpha : Type} (raw needle acc bit rest : OTerm alpha) :
    (matrix raw).subst (Sum.elim Term.var (fun i => emb (![needle,acc,bit,rest] i))) =
      (fields raw needle acc bit rest).imp (flags raw needle bit) := by
  let tape : Fin 4 → OTerm alpha := ![needle,acc,bit,rest]
  let terms : alpha ⊕ Fin 4 → OTerm alpha := Sum.elim Term.var tape
  have he : (Sum.elim Term.var (fun i => emb (tape i))) =
      (fun a => emb (terms a)) := by
    funext a
    cases a <;> rfl
  have held : (raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 4)).subst terms = raw :=
    InternalRecursionGraphSyntaxProof.witnessLift raw tape
  have h0 : (Term.var (.inr (0 : Fin 4)) : OTerm (alpha ⊕ Fin 4)).subst terms = needle := rfl
  have h1 : (Term.var (.inr (1 : Fin 4)) : OTerm (alpha ⊕ Fin 4)).subst terms = acc := rfl
  have h2 : (Term.var (.inr (2 : Fin 4)) : OTerm (alpha ⊕ Fin 4)).subst terms = bit := rfl
  have h3 : (Term.var (.inr (3 : Fin 4)) : OTerm (alpha ⊕ Fin 4)).subst terms = rest := rfl
  change (matrix raw).subst (Sum.elim Term.var (fun i => emb (tape i))) = _
  rw [he]
  unfold matrix
  rw [impSubst,fieldsSubst,flagsSubst,held,h0,h1,h2,h3]

theorem predicateInstantiate {alpha : Type} (raw : OTerm alpha) :
    instantiate (predicate) (emb raw) = AtRaw raw := by
  rw [predicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

@[simp] theorem belowRawRename {alpha beta : Type} (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw raw).relabel j = BelowRaw (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold predicate
  rw [atRawRename]
  rfl

theorem predicateLift {alpha : Type} :
    lift (predicate (alpha := alpha)) = predicate (alpha := alpha ⊕ Fin 1) := by
  unfold lift predicate
  rw [atRawRename]
  rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseFlagsInductionSyntaxProof
