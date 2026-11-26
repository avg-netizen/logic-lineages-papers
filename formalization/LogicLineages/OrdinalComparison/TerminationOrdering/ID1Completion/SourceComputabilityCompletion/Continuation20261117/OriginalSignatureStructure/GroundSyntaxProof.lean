module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalSignatureStructure.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalSignatureStructure.GroundSyntaxProof
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
open Continuation20261116.OriginalConcreteHeadSignature
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def result (bound out index : OTerm alpha) : Formula alpha :=
  (graph1 OriginalContextInsertion.length bound out) ⊓
  (graph2 InternalRawListRecursion.lookup z index out)
def rowBody (bound : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  (graph1 groundList (.var (.inr 0)) (bound.relabel Sum.inl)).imp
    (result (bound.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)))
def row (bound : OTerm alpha) : Formula alpha := allBlock (rowBody bound)

theorem resultSubst {beta : Type} (bound out index : OTerm alpha) (ts : alpha → OTerm beta) :
    (result bound out index).subst (fun a => emb (ts a)) =
      result (bound.subst ts) (out.subst ts) (index.subst ts) := by
  simp only [result,InternalRecursionClosureSyntaxProof.conjunctionSubst,impSubst,
    graph1,graph2,programSubst,consTermSubst,emptySubst,zSubst]

theorem resultRename {beta : Type} (bound out index : OTerm alpha) (j : alpha → beta) :
    (result bound out index).relabel j = result (bound.relabel j) (out.relabel j) (index.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (result bound out index).subst (fun a => emb (.var (j a))) = _
  rw [resultSubst]
  simp only [← termRelabelAsSubst]

theorem rowSubst {beta : Type} (bound : OTerm alpha) (ts : alpha → OTerm beta) :
    (row bound).subst (fun a => emb (ts a)) = row (bound.subst ts) := by
  unfold row rowBody
  rw [allBlockSubst,liftedEmbedding,impSubst,resultSubst]
  simp only [graph1,programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

theorem rowRename {beta : Type} (bound : OTerm alpha) (j : alpha → beta) :
    (row bound).relabel j = row (bound.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row bound).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]

theorem rowBodyWitness (bound out index : OTerm alpha) :
    (rowBody bound).subst (Sum.elim Term.var (fun i => emb (![out,index] i))) =
      (graph1 groundList out bound).imp (result bound out index) := by
  have he : (Sum.elim Term.var (fun i => emb (![out,index] i))) =
      (fun a => emb (Sum.elim Term.var ![out,index] a)) := by
    funext a
    cases a <;> rfl
  unfold rowBody
  rw [he,impSubst,resultSubst]
  simp only [graph1,programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rowInstantiate (bound : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
    instantiate (row bound) (emb t) = row (bound.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (bound : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (row bound) = row (bound.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (bound out index : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row bound)))
    (hg : Nonempty (Derivation body Delta (graph1 groundList out bound))) :
    Nonempty (Derivation body Delta (result bound out index)) := by
  have h := actualFiniteUniversalElimination body alpha 2 Delta (rowBody bound)
    (fun i => emb (![out,index] i)) hr
  rw [rowBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hg⟩ := hg
  exact ⟨Derivation.implicationElimination h hg⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalSignatureStructure.GroundSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalSignatureStructure.GroundSyntaxProof
