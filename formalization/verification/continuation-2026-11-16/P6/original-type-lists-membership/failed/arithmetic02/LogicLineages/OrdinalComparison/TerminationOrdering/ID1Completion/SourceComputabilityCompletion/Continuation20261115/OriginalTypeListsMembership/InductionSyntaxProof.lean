module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.MemberSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.LengthSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.InductionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalTagArithmeticSyntaxProof hiding OTerm row rowInstantiate rowSuccessor
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalOriginalOrderSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open OriginalContextInsertionSyntaxProof
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def condition (bound allowed types len : OTerm alpha) : Formula alpha :=
  InternalLessThan.strictLess len (suc bound) ⊓ Targets.allMembers types allowed
def fields (bound allowed out types len : OTerm alpha) : Formula alpha :=
  graph2 OriginalTypeListsEnumeration.enumeration out bound allowed ⊓ OriginalContextInsertion.lengthGraph len types
def result (bound allowed out types len : OTerm alpha) : Formula alpha :=
  ((graph2 contains (numeral 1) out types).imp (condition bound allowed types len)) ⊓
  ((condition bound allowed types len).imp (graph2 contains (numeral 1) out types))
def rowBody (bound : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  (fields (bound.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))).imp
    (result (bound.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)))
def row (bound : OTerm alpha) : Formula alpha := allBlock (rowBody bound)

theorem conditionSubst {beta : Type} (bound allowed types len : OTerm alpha) (ts : alpha → OTerm beta) :
    (condition bound allowed types len).subst (fun a => emb (ts a)) =
      condition (bound.subst ts) (allowed.subst ts) (types.subst ts) (len.subst ts) := by
  simp only [condition,conjunctionSubst,MemberSyntaxProof.membersSubst,InternalLessThan.strictLess,
    InternalQuotientComparisonSyntaxProof.orderSubst,sucSubst]

theorem fieldsSubst {beta : Type} (bound allowed out types len : OTerm alpha) (ts : alpha → OTerm beta) :
    (fields bound allowed out types len).subst (fun a => emb (ts a)) =
      fields (bound.subst ts) (allowed.subst ts) (out.subst ts) (types.subst ts) (len.subst ts) := by
  simp only [fields,conjunctionSubst,graph2,programSubst,consTermSubst,emptySubst,lengthSubst]

theorem resultSubst {beta : Type} (bound allowed out types len : OTerm alpha) (ts : alpha → OTerm beta) :
    (result bound allowed out types len).subst (fun a => emb (ts a)) =
      result (bound.subst ts) (allowed.subst ts) (out.subst ts) (types.subst ts) (len.subst ts) := by
  simp only [result,conjunctionSubst,impSubst,conditionSubst,graph2,programSubst,
    consTermSubst,emptySubst,numeral,zSubst,sucSubst]

theorem resultRename {beta : Type} (bound allowed out types len : OTerm alpha) (j : alpha → beta) :
    (result bound allowed out types len).relabel j =
      result (bound.relabel j) (allowed.relabel j) (out.relabel j) (types.relabel j) (len.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (result bound allowed out types len).subst (fun a => emb (.var (j a))) = _
  rw [resultSubst]
  simp only [← termRelabelAsSubst]

theorem rowSubst {beta : Type} (bound : OTerm alpha) (ts : alpha → OTerm beta) :
    (row bound).subst (fun a => emb (ts a)) = row (bound.subst ts) := by
  unfold row rowBody
  rw [allBlockSubst,liftedEmbedding,impSubst,fieldsSubst,resultSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem rowRename {beta : Type} (bound : OTerm alpha) (j : alpha → beta) :
    (row bound).relabel j = row (bound.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row bound).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]

theorem rowBodyWitness (bound allowed out types len : OTerm alpha) :
    (rowBody bound).subst (Sum.elim Term.var (fun i => emb (![allowed,out,types,len] i))) =
      (fields bound allowed out types len).imp (result bound allowed out types len) := by
  have he : (Sum.elim Term.var (fun i => emb (![allowed,out,types,len] i))) =
      (fun a => emb (Sum.elim Term.var ![allowed,out,types,len] a)) := by
    funext a
    cases a <;> rfl
  unfold rowBody
  rw [he,impSubst,fieldsSubst,resultSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rowInstantiate (bound : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
    instantiate (row bound) (emb t) = row (bound.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (bound : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (row bound) = row (bound.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (bound allowed out types len : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row bound)))
    (hg : Nonempty (Derivation body Delta (fields bound allowed out types len))) :
    Nonempty (Derivation body Delta (result bound allowed out types len)) := by
  have h := actualFiniteUniversalElimination body alpha 4 Delta (rowBody bound)
    (fun i => emb (![allowed,out,types,len] i)) hr
  rw [rowBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hg⟩ := hg
  exact ⟨Derivation.implicationElimination h hg⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.InductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.InductionSyntaxProof
