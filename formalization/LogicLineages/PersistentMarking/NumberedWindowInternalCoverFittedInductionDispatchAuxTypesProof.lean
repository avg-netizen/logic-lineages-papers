module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedInductionDispatchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowParentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowResultTypeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardOpenProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedInductionDispatchAuxTypesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalSettingsGrammarGuardOpenProof (exact_OpenSettingsRefitGuardReports)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow strictAuxChildren)
open NumberedWindowInternalStrictAuxWindowParentProof (exact_OpenStrictAuxWindowParent)
open NumberedWindowInternalStrictAuxWindowResultTypeProof (exact_OpenStrictAuxWindowResultType)
open NumberedWindowInternalCoverRefinedInductionDispatchTransportProof (moveWindowType)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets
open NumberedWindowInternalCoverFittedInductionDispatchTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem toActualK (s : Settings) (TW : Program 1) (ty : OTerm α)
    (actual : Derivation body Γ (unary (refitGuard s TW) (suc z) ty)) :
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) := by
  obtain ⟨rule⟩ := exact_OpenSettingsRefitGuardReports s TW body α Γ ty
  exact ⟨Derivation.conjunctionRight (Derivation.implicationElimination (Derivation.conjunctionLeft rule) actual)⟩

theorem exact_OpenFittedAuxTypes (V TV M : Program 1) (B : Program 2) (TW : Program 1)
    (s : Settings) (raw p vertices ctx result dom cod fn arg : OTerm α)
    (row : PackedRow (fittedPrograms s V TV M B TW) s body Γ raw (auxiliaryTerm dom cod fn arg)
      p vertices ctx result 6 [dom,cod,fn,arg]) :
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) dom)) ∧
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) cod)) := by
  let A := fittedWindowBase s B
  let T := refitGuard s TW
  let W := strictAuxWindow A T
  let key := auxiliaryTerm dom cod fn arg
  obtain ⟨same⟩ := exact_OpenStrictAuxWindowResultType A T body α Γ ctx result dom cod fn arg row.data.typed
  have typed := moveWindowType W ctx result cod key same row.data.typed
  obtain ⟨children⟩ := exact_OpenStrictAuxWindowParent A T body α Γ ctx dom cod fn arg typed
  have guards : Derivation body Γ (unary T (suc z) dom ⊓ unary T (suc z) cod) :=
    Derivation.conjunctionLeft children
  exact ⟨toActualK s TW dom (Derivation.conjunctionLeft guards),
    toActualK s TW cod (Derivation.conjunctionRight guards)⟩

#print axioms exact_OpenFittedAuxTypes

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedInductionDispatchAuxTypesProof
