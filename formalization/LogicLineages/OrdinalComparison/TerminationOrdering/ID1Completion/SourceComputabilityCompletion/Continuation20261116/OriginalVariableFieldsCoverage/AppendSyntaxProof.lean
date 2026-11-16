module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionShiftInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.AppendSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalGraphCompositionSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalClosedPrograms
open InternalListInduction
open InternalTagArithmeticSyntaxProof (emb zRelabel)
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof

def appendIdentity {beta : Type} (code : OTerm beta) : Formula beta :=
  graph2 InternalApplicationValidityStackAppend.append code code z

theorem identitySubst {beta : Type} (code : OTerm alpha) (ts : alpha → OTerm beta) :
    (appendIdentity code).subst (fun a => emb (ts a)) = appendIdentity (code.subst ts) := by
  simp only [appendIdentity,InternalApplicationValidityStackAppendSyntaxProof.graph2Subst,InternalTagArithmeticSyntaxProof.zSubst]

theorem identityRename {beta : Type} (code : OTerm alpha) (j : alpha → beta) :
    (appendIdentity code).relabel j = appendIdentity (code.relabel j) := by
  simp only [appendIdentity,graph2Rename,zRelabel]

theorem identityAtCode (code : OTerm alpha) :
    atCode (appendIdentity (.var (.inr (0 : Fin 1))) : Formula (alpha ⊕ Fin 1)) code =
      appendIdentity code := by
  simp only [atCode,instantiate,InternalTagArithmeticSyntaxProof.bindEmbedding,identitySubst,InternalTagArithmeticSyntaxProof.varBind]

theorem identityAtIndex (i : Fin 3) :
    atIndex (appendIdentity (.var (.inr (0 : Fin 1))) : Formula (alpha ⊕ Fin 1)) i =
      appendIdentity (.var (.inr i)) := by
  rw [atIndex,identityRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.AppendSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.AppendSyntaxProof
