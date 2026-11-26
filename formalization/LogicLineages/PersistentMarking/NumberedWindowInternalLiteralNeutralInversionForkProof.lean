module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralApplicationRowsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDecoratedAddressedCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralInversionForkProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalComputabilityDownwardSyntaxProof (edgeRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof (inputsRename)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalAtomicRefinement (bottomSource)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource)
open NumberedWindowInternalNeutralFactsTargets (direct atom)
open NumberedWindowInternalNeutralFactsSyntaxProof (atomRename)
open NumberedWindowInternalLiteralCoveredTypedAuxCasesProof (ActiveRaw)
open NumberedWindowInternalLiteralFunctionGuardInversionProof (Parts)
open NumberedWindowInternalLiteralCoveredMemo (coveredMemoWindow)
open NumberedWindowInternalLiteralCoveredMemoAuxRowProof (childAtWindow)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralApplicationLeastDecoratorProof (auxiliaryDecorator)
open NumberedWindowInternalLiteralNeutralApplicationRowsProof (exact_OpenNeutralApplicationRows)
open NumberedWindowInternalLiteralDecoratedAddressedCasesProof (exact_OpenDecoratedApplicationDirectCases)

attribute [local irreducible] programGraph
variable {α : Type} {Γ : List (Formula α)}

/-- Exact remaining child case in application inversion. A genuine
accepted application followed by a genuine direct certificate from
its result reaches this continuation only for an actual contextual
function-child row. No separate input or output decoding hypotheses
are requested. For full inversion, take goal to be the original
inherited-application formula and pay this remaining continuation. -/
theorem exact_OpenLiteralNeutralInversionFromChild
    (C : Program 3) (X : Program 2) (s : Settings)
    (leaf : Nat → Program 3) (other : Program 3) (base : Program 2) (T V i cv tv : Program 1)
    (L₀ : Program 3) (c : Nat) (x u t y : OTerm α) (goal : Formula α) :
    let W := coveredMemoWindow C s base T V
    let raw := ActiveRaw C s leaf other base T V
    let L := guardedLeast (headerLeast (auxiliaryDecorator L₀))
    let R := rawWithTarget i cv tv (guardedRaw raw) L
    let data := S i cv tv R L
    let B := sourceBody data c
    D B Γ (atom neutralSource x) →
    D B Γ (programGraph (applicationGuard i L) (suc z) ![x,u,t]) →
    D B Γ (direct data (hop cv tv R L) c t y) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (ctx result dom cod fn arg k sc st before after cert q w r d e f a child d' e' g a' : OTerm β),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
      D B Δ (unary i (suc z) (x.relabel j)) → D B Δ (unary i (suc z) (u.relabel j)) →
      D B Δ (parsedApplicationInputs (x.relabel j) (u.relabel j) ctx result dom cod fn arg) →
      D B Δ (addressReport (y.relabel j) sc st after) →
      D B Δ (eqn sc ctx) → D B Δ (eqn st cod) → D B Δ (eqn before k) →
      D B Δ (programGraph L (suc before) ![sc,st,auxiliaryTerm dom cod fn arg]) →
      Parts B Δ q w r d e f a child d' e' g a' →
      D B Δ (programGraph raw (suc z) ![sc,rawCons d e,f,child,g] ⊓
        (childAtWindow W V sc d a ⊓ (hasLeast C X W s sc (rawCons d e) f ⊓
          (hasLeast C X W s sc (rawCons d e) g ⊓ hasLeast C X W s sc d a)))) →
      D B Δ (hopCalls R L sc st before cert after q w r) → D B Δ (goal.relabel j)) →
    D B Γ (atom bottomSource y ⊔ goal) := by
  intro W raw L R data B neutral accepted step use
  let disj := atom bottomSource y ⊔ goal
  apply exact_OpenNeutralApplicationRows i L x u t disj neutral accepted
  intro β j Δ ctx result dom cod fn arg k header keep left right parsed least address head notLambda
  change D B Δ ((atom bottomSource y).relabel j ⊔ goal.relabel j)
  rw [atomRename]
  have step' := renameInto step j Δ keep
  simp only [direct,edgeRename] at step'
  apply exact_OpenDecoratedApplicationDirectCases C X s leaf other base T V i cv tv L₀ c
    (t.relabel j) (y.relabel j) ctx dom cod fn arg k header (goal.relabel j)
    address least head notLambda step'
  intro γ m Ξ sc st before after cert q w r d e f a child d' e' g a' h traced ec et eb app parts fits calls
  let n := m ∘ j
  have keepN (φ : Formula α) (used : φ ∈ Γ) : φ.relabel n ∈ Ξ := by
    simpa only [n,formulaRelabelComposition] using h _ (keep φ used)
  have l := renameInto left m Ξ h
  have r' := renameInto right m Ξ h
  simp only [unaryRename,sucRelabel,zRelabel,n,Term.relabel_relabel] at l r'
  have p := renameInto parsed m Ξ h
  simp only [inputsRename,n,Term.relabel_relabel] at p
  have finish := use γ n Ξ (ctx.relabel m) (result.relabel m) (dom.relabel m) (cod.relabel m)
    (fn.relabel m) (arg.relabel m) (k.relabel m) sc st before after cert q w r d e f a child d' e' g a'
    keepN l r' p (by simpa only [n,Term.relabel_relabel] using traced)
    ec et eb app parts fits calls
  simpa only [n,formulaRelabelComposition] using finish

#print axioms exact_OpenLiteralNeutralInversionFromChild
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralInversionForkProof
