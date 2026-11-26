module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedSelectedFormationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalApplicationFormationInterfaceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginalSelectedFormationAtGuardProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalSettingsGrammarGuardOpenProof (exact_OpenSettingsRefitGuardReports)
open NumberedWindowInternalOriginalApplicationFormationInterfaceProof
open NumberedWindowInternalMeasuredUnrestrictedSelectedFormationInputsProof (selectedWindow Inputs)
open NumberedWindowInternalMeasuredUnrestrictedSelectedFormationProof
open NumberedWindowInternalCoverCombinedRestrictedFormationTargets (thinFormation)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem split (s : Settings) (T TV : Program 1) (ty : OTerm α)
    (held : Nonempty (Derivation B Γ (unary (conjunction (refitGuard s T) TV) (suc z) ty))) :
    Nonempty (Derivation B Γ (unary TV (suc z) ty ⊓ memberGraph (typesTerm s α) ty)) := by
  obtain ⟨data⟩ := conjunctionRecover (refitGuard s T) TV ![ty] held
  obtain ⟨take⟩ := exact_OpenSettingsRefitGuardReports s T B α Γ ty
  have inside := Derivation.implicationElimination (Derivation.conjunctionLeft take)
    (Derivation.conjunctionLeft data)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionRight data)
    (Derivation.conjunctionRight inside)⟩

/-- In the actual selected-grammar window whose intrinsic type guard
literally calls T, the grammar membership and TV, the held two guard
outputs and held genuine argument window imply real parent formation. -/
theorem exact_OpenOriginalSelectedGuardParentClosure (s : Settings) (base : Program 2)
    (T V TV baseM : Program 1) (ctx dom cod arg : OTerm α) :
    let Tg := conjunction (refitGuard s T) TV
    let W := selectedWindow s base Tg V TV baseM
    Nonempty (Derivation B Γ (unary Tg (suc z) dom ⊓ unary Tg (suc z) cod)) →
    Nonempty (Derivation B Γ (windowAt W ctx dom arg)) →
    OriginalParentClosureAt W B Γ ctx dom cod arg := by
  intro Tg W held argWindow β j Δ f keep fn
  have moved := renameInto held j Δ keep
  rw [conjunctionRename,unaryRename,unaryRename,sucRelabel,zRelabel] at moved
  have a := renameInto argWindow j Δ keep
  rw [windowRename] at a
  obtain ⟨m⟩ := moved
  obtain ⟨dg⟩ := split s T TV (dom.relabel j) ⟨Derivation.conjunctionLeft m⟩
  obtain ⟨cg⟩ := split s T TV (cod.relabel j) ⟨Derivation.conjunctionRight m⟩
  have h : Inputs s W Tg TV B Δ (ctx.relabel j) (dom.relabel j) (cod.relabel j) f (arg.relabel j) :=
    ⟨fn,a,⟨m⟩,⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft dg) (Derivation.conjunctionLeft cg)⟩,
      ⟨Derivation.conjunctionRight dg⟩,⟨Derivation.conjunctionRight cg⟩⟩
  exact exact_OpenUnrestrictedSelectedFormation s base Tg V TV baseM
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) f (arg.relabel j) h

theorem exact_OpenOriginalSelectedGuardFormation (s : Settings) (base : Program 2)
    (T V TV baseM : Program 1) (ctx dom cod arg : OTerm α) :
    let Tg := conjunction (refitGuard s T) TV
    let W := selectedWindow s base Tg V TV baseM
    Nonempty (Derivation B Γ (unary Tg (suc z) dom ⊓ unary Tg (suc z) cod)) →
    Nonempty (Derivation B Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation B Γ (thinFormation W ctx dom cod arg)) := by
  intro Tg W types argument
  exact exact_OriginalThinFormationFromParentClosure W ctx dom cod arg
    (exact_OpenOriginalSelectedGuardParentClosure s base T V TV baseM ctx dom cod arg types argument)

#print axioms exact_OpenOriginalSelectedGuardParentClosure
#print axioms exact_OpenOriginalSelectedGuardFormation
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginalSelectedFormationAtGuardProof
