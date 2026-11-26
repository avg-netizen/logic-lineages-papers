module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedOwnEarlierProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowResultTypeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchRecursiveProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof (lambdaRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverRefinedOwnEarlierProof
  (exact_OpenCoverRefinedLambdaOwnEarlier exact_OpenCoverRefinedAuxOwnEarlier)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalStrictAuxWindowResultTypeProof (exact_OpenStrictAuxWindowResultType)
open NumberedWindowInternalCoverRefinedInductionDispatchTransportProof (renameRow moveMemberKey moveWindowType)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem atLambda (V TV M : Program 1) (B : Program 2) (TW : Program 1) (s : Settings)
    (raw p vertices ctx result ty q : OTerm α)
    (need : Obligations (refinedPrograms V TV M B TW) s body)
    (row : PackedRow (refinedPrograms V TV M B TW) s body Γ raw (lambdaTerm ty q) p vertices ctx result 2 [ty,q]) :
    Nonempty (Derivation body Γ (memberGraph vertices raw)) := by
  let P := refinedPrograms V TV M B TW
  apply need.lambdaBody α Γ raw p vertices ctx result ty q _ row
  intro β j Δ keep facts
  rw [graphRename]
  obtain ⟨bodyTy,arrowEq,typedBody,annotation⟩ := facts
  have parent := renameRow P s j keep row.data
  rw [lambdaRename] at parent
  have packed := renameInto row.packed j Δ keep
  rw [eqnRelabel,lambdaRename] at packed
  obtain ⟨packed⟩ := packed
  have hit := exact_OpenCoverRefinedLambdaOwnEarlier V TV M (strictAuxWindow B TW) s body β Δ
    (p.relabel j) (vertices.relabel j) (rawCons (ty.relabel j) (ctx.relabel j)) bodyTy (ty.relabel j) (q.relabel j)
    parent.parent parent.branchBelow typedBody annotation
  exact moveMemberKey (vertices.relabel j) (lambdaTerm (ty.relabel j) (q.relabel j))
    (raw.relabel j) (symm packed) hit

theorem atAux (V TV M : Program 1) (B : Program 2) (TW : Program 1) (s : Settings)
    (raw p vertices ctx result dom cod fn arg : OTerm α)
    (need : Obligations (refinedPrograms V TV M B TW) s body)
    (row : PackedRow (refinedPrograms V TV M B TW) s body Γ raw (auxiliaryTerm dom cod fn arg)
      p vertices ctx result 6 [dom,cod,fn,arg]) :
    Nonempty (Derivation body Γ (memberGraph vertices raw)) := by
  let W := strictAuxWindow B TW
  let key := auxiliaryTerm dom cod fn arg
  obtain ⟨actualResult⟩ := exact_OpenStrictAuxWindowResultType B TW body α Γ ctx result dom cod fn arg row.data.typed
  have typed := moveWindowType W ctx result cod key actualResult row.data.typed
  have actualK := need.auxTypes α Γ raw p vertices ctx result dom cod fn arg row
  have hit := exact_OpenCoverRefinedAuxOwnEarlier V TV M B TW s body α Γ p vertices ctx dom cod fn arg
    row.data.parent row.data.branchBelow typed actualK.1 actualK.2
  obtain ⟨packed⟩ := row.packed
  exact moveMemberKey vertices key raw (symm packed) hit

#print axioms atLambda
#print axioms atAux

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchRecursiveProof
