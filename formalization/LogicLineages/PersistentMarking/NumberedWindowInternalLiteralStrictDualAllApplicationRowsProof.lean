module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictDualChildProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationRowsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictDualAddressedAllAuxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictDualAllApplicationRowsProof
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
open NumberedWindowInternalLiteralFunctionGuardInversionProof (Parts)
open NumberedWindowInternalLiteralCoveredMemo (coveredMemoWindow)
open NumberedWindowInternalLiteralStrictSealedWindowProof (strictSealedWindow)
open NumberedWindowInternalLiteralStrictDualChildProof (strictDualRaw)
open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (fullAuxiliaryDecorator)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalLiteralCoveredMemoAuxRowProof (childAtWindow)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralApplicationRowsProof (exact_OpenLiteralApplicationRows)
open NumberedWindowInternalLiteralRootDispatchOpenProof (bit)
open NumberedWindowInternalLiteralAuxRootLeaf (functionLambdaHeader)
open NumberedWindowInternalSparseRawRunRootTargets (rootWitnessTerm)
open NumberedWindowInternalLiteralStrictDualAddressedAllAuxProof (exact_OpenStrictDualAddressedAllAux)

attribute [local irreducible] programGraph
variable {α : Type} {Γ : List (Formula α)}

/-- Actual applications followed by a checked direct step accept no
extra shape hypotheses. Beta and function-child continuations are
given the exact accepted original application and certificate reports. -/
theorem exact_OpenStrictDualAllApplicationRows
    (C : Program 3) (X : Program 2) (s : Settings)
    (leaf : Nat → Program 3) (other : Program 3) (rawBase base : Program 2) (rawT V T i cv tv : Program 1)
    (L₀ : Program 3) (c : Nat) (x u t y : OTerm α) (goal : Formula α) :
    let W := coveredMemoWindow C s rawBase rawT V
    let Z := strictSealedWindow C s base T
    let raw := strictDualRaw C s leaf other rawBase base rawT V T
    let L := guardedLeast (headerLeast (fullAuxiliaryDecorator L₀))
    let R := rawWithTarget i cv tv (guardedRaw raw) L
    let data := S i cv tv R L
    let B := sourceBody data c
    D B Γ (programGraph (applicationGuard i L) (suc z) ![x,u,t]) →
    D B Γ (direct data (hop cv tv R L) c t y) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (ctx result dom cod fn arg k sc st before after cert q w r payload : OTerm β),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
      D B Δ (unary i (suc z) (x.relabel j)) → D B Δ (unary i (suc z) (u.relabel j)) →
      D B Δ (parsedApplicationInputs (x.relabel j) (u.relabel j) ctx result dom cod fn arg) →
      D B Δ (addressReport (y.relabel j) sc st after) →
      D B Δ (eqn sc ctx) → D B Δ (eqn st cod) → D B Δ (eqn before k) →
      D B Δ (programGraph L (suc before) ![sc,st,auxiliaryTerm dom cod fn arg]) →
      D B Δ (eqn w (rootWitnessTerm payload)) → D B Δ (bit (leaf 6) ![q,payload,r]) →
      D B Δ (bit functionLambdaHeader ![q,payload,r]) →
      D B Δ (hopCalls R L sc st before cert after q w r) → D B Δ (goal.relabel j)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (ctx result dom cod fn arg k sc st before after cert q w r d e f a child d' e' g a' : OTerm β),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
      D B Δ (unary i (suc z) (x.relabel j)) → D B Δ (unary i (suc z) (u.relabel j)) →
      D B Δ (parsedApplicationInputs (x.relabel j) (u.relabel j) ctx result dom cod fn arg) →
      D B Δ (addressReport (y.relabel j) sc st after) →
      D B Δ (eqn sc ctx) → D B Δ (eqn st cod) → D B Δ (eqn before k) →
      D B Δ (programGraph L (suc before) ![sc,st,auxiliaryTerm dom cod fn arg]) →
      Parts B Δ q w r d e f a child d' e' g a' →
      D B Δ (programGraph (guardedRaw raw) (suc z) ![sc,rawCons d e,f,child,g] ⊓
        (childAtWindow W V sc d a ⊓ (hasLeast C X W s sc (rawCons d e) f ⊓
          (hasLeast C X W s sc (rawCons d e) g ⊓ hasLeast C X W s sc d a)))) →
      D B Δ (windowAt Z sc (rawCons d e) f ⊓ (windowAt Z sc (rawCons d e) g ⊓ windowAt Z sc d a)) →
      D B Δ (hopCalls R L sc st before cert after q w r) → D B Δ (goal.relabel j)) →
    D B Γ (atom bottomSource y ⊔ goal) := by
  intro W Z raw L R data B accepted step beta use
  let disj := atom bottomSource y ⊔ goal
  apply exact_OpenLiteralApplicationRows i L x u t disj accepted
  intro β j Δ ctx result dom cod fn arg k keep left right parsed least address
  change D B Δ ((atom bottomSource y).relabel j ⊔ goal.relabel j)
  rw [atomRename]
  have step' := renameInto step j Δ keep
  simp only [direct,edgeRename] at step'
  apply exact_OpenStrictDualAddressedAllAux C X s leaf other rawBase base rawT V T i cv tv L₀ c
    (t.relabel j) (y.relabel j) ctx dom cod fn arg k (goal.relabel j)
    address least step'
  · intro γ m Ξ sc st before after cert q w r payload h traced ec et eb app witness rule head calls
    let n := m ∘ j
    have keepN (φ : Formula α) (used : φ ∈ Γ) : φ.relabel n ∈ Ξ := by
      simpa only [n,formulaRelabelComposition] using h _ (keep φ used)
    have l := renameInto left m Ξ h
    have r' := renameInto right m Ξ h
    simp only [unaryRename,sucRelabel,zRelabel,n,Term.relabel_relabel] at l r'
    have p := renameInto parsed m Ξ h
    simp only [inputsRename,n,Term.relabel_relabel] at p
    have finish := beta γ n Ξ (ctx.relabel m) (result.relabel m) (dom.relabel m) (cod.relabel m)
      (fn.relabel m) (arg.relabel m) (k.relabel m) sc st before after cert q w r payload
      keepN l r' p (by simpa only [n,Term.relabel_relabel] using traced)
      ec et eb app witness rule head calls
    simpa only [n,formulaRelabelComposition] using finish
  · intro γ m Ξ sc st before after cert q w r d e f a child d' e' g a' h traced ec et eb app parts fits strict calls
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
      ec et eb app parts fits strict calls
    simpa only [n,formulaRelabelComposition] using finish

#print axioms exact_OpenStrictDualAllApplicationRows
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictDualAllApplicationRowsProof
