module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.WitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.CombineWitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalRecursionClosureSyntaxProof
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def fields (n : Nat) (out answers ts hs ls tb vb prior opened value : OTerm alpha) : Formula alpha :=
  graph2 InternalRawListRecursion.lookup prior z answers ⊓
    graph2 InternalRawListRecursion.lookup opened (numeral 1) answers ⊓
    programGraph (OriginalEnumerationConstructorLayer.layer n) value ![ts,hs,ls,tb,vb,prior,opened] ⊓
    eqn out (suc value)

def matrix (n : Nat) (out answers ts hs ls tb vb : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  fields n (out.relabel Sum.inl) (answers.relabel Sum.inl) (ts.relabel Sum.inl) (hs.relabel Sum.inl)
    (ls.relabel Sum.inl) (tb.relabel Sum.inl) (vb.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))

theorem fieldsSubst {beta : Type} (n : Nat)
    (out answers ts hs ls tb vb prior opened value : OTerm alpha) (sub : alpha → OTerm beta) :
    (fields n out answers ts hs ls tb vb prior opened value).subst (fun a => emb (sub a)) =
      fields n (out.subst sub) (answers.subst sub) (ts.subst sub) (hs.subst sub) (ls.subst sub)
        (tb.subst sub) (vb.subst sub) (prior.subst sub) (opened.subst sub) (value.subst sub) := by
  simp only [fields,conjunctionSubst,graph2,InternalComputabilityApplicationSyntaxProof.programSubst,
    consTermSubst,emptySubst,eqnSubst,sucSubst,numeral,zSubst]

theorem matrixWitness (n : Nat) (out answers ts hs ls tb vb : OTerm alpha) (ys : Fin 3 → OTerm alpha) :
    (matrix n out answers ts hs ls tb vb).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      fields n out answers ts hs ls tb vb (ys 0) (ys 1) (ys 2) := by
  have he : Sum.elim Term.var (fun i => emb (ys i)) =
      (fun a => emb (Sum.elim Term.var ys a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he,fieldsSubst]
  simp only [InternalRecursionGraphSyntaxProof.witnessLift,Term.subst,Sum.elim_inr]

theorem positiveSubst {beta : Type} (n : Nat) (out answers ts hs ls tb vb : OTerm alpha)
    (sub : alpha → OTerm beta) :
    (Targets.positiveOutput n out answers ts hs ls tb vb).subst (fun a => emb (sub a)) =
      Targets.positiveOutput n (out.subst sub) (answers.subst sub) (ts.subst sub) (hs.subst sub)
        (ls.subst sub) (tb.subst sub) (vb.subst sub) := by
  change (InternalFiniteBlocks.block (matrix n out answers ts hs ls tb vb)).subst (fun a => emb (sub a)) =
    InternalFiniteBlocks.block (matrix n (out.subst sub) (answers.subst sub) (ts.subst sub) (hs.subst sub)
      (ls.subst sub) (tb.subst sub) (vb.subst sub))
  unfold matrix
  rw [OriginalContextInsertionSyntaxProof.blockSubst,liftedEmbedding,fieldsSubst]
  simp only [InternalRecursionGraphSyntaxProof.liftSubst,Term.subst,Sum.elim_inr]

theorem positiveRename {beta : Type} (n : Nat) (out answers ts hs ls tb vb : OTerm alpha) (j : alpha → beta) :
    (Targets.positiveOutput n out answers ts hs ls tb vb).relabel j =
      Targets.positiveOutput n (out.relabel j) (answers.relabel j) (ts.relabel j) (hs.relabel j)
        (ls.relabel j) (tb.relabel j) (vb.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Targets.positiveOutput n out answers ts hs ls tb vb).subst (fun a => emb (.var (j a))) = _
  rw [positiveSubst]
  simp only [← termRelabelAsSubst]

theorem introduce (n : Nat) (out answers ts hs ls tb vb : OTerm alpha) (ys : Fin 3 → OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields n out answers ts hs ls tb vb (ys 0) (ys 1) (ys 2)))) :
    Nonempty (Derivation body Delta (Targets.positiveOutput n out answers ts hs ls tb vb)) := by
  change Nonempty (Derivation body Delta (InternalFiniteBlocks.block (matrix n out answers ts hs ls tb vb)))
  apply InternalFiniteBlocksProof.introduction body alpha 3 Delta _ (fun i => emb (ys i))
  rw [matrixWitness]
  exact hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.CombineWitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.CombineWitnessProof
