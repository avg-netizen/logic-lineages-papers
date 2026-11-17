module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GenericInductionMatrixSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph2)
open InternalTagArithmeticSyntaxProof (emb zSubst sucSubst)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTermSubstitutionProof InternalFiniteBlocksSubstitutionProof InternalBinderTransportProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalAdditionLawsProof
open InternalRawListRecursionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph
/-- Proof-only schema; no concrete program AST or concrete Meaning is imported. -/
def matrix {alpha : Type} (pair enum member : Program 2)
    (fuel : OTerm alpha) (meaning : Formula (alpha ⊕ Fin 11)) : Formula (alpha ⊕ Fin 11) :=
  let v (i : Fin 11) : OTerm (alpha ⊕ Fin 11) := .var (.inr i)
  let observations := graph2 pair (v 0) (v 6) (fuel.relabel Sum.inl) ⊓
    graph2 pair (v 1) (v 7) (v 2) ⊓
    graph2 pair (v 2) (v 8) (v 3) ⊓
    graph2 pair (v 3) (v 9) (v 10) ⊓
    graph2 enum (v 4) (v 0) (v 1)
  let membership := graph2 member (numeral 1) (v 4) (v 5)
  observations.imp ((membership.imp meaning) ⊓ (meaning.imp membership))

theorem allSubst {alpha beta : Type} (pair enum member : Program 2)
    (fuel : OTerm alpha) (ts : alpha → OTerm beta)
    (meaning : Formula (alpha ⊕ Fin 11)) (meaning' : Formula (beta ⊕ Fin 11))
    (hm : meaning.subst (fun a => emb (Sum.elim
      (fun x => (ts x).relabel Sum.inl) (fun i : Fin 11 => (.var (.inr i) : OTerm (beta ⊕ Fin 11))) a)) = meaning') :
    (InternalClosedPrograms.allBlock (matrix pair enum member fuel meaning)).subst (fun a => emb (ts a)) =
      InternalClosedPrograms.allBlock (matrix pair enum member (fuel.subst ts) meaning') := by
  rw [allBlockSubst,liftedEmbedding]
  unfold matrix
  simp only [impSubst,conjunctionSubst,hm,InternalApplicationValidityStackAppendSyntaxProof.graph2Subst,
    SourceComputabilityFormulaSupportProof.numeral,zSubst,sucSubst,
    liftSubst,Term.subst,Sum.elim_inr]
  all_goals rfl
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GenericInductionMatrixSyntaxProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GenericInductionMatrixSyntaxProof
