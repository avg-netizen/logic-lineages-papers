module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedCanonicalChildProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictSealedWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSealedWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictChildSelectionProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalOriginalFirstHopCoreProof (literalAddress)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (D finiteScalar)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralLeastOnFixedPointProof (WindowEndpoints casesLeastOn)
open NumberedWindowInternalLiteralLeastOnCoverageProof (exact_OpenLeastOnFromCoverage)
open NumberedWindowInternalLiteralEdgeObserversProof (withObservers)
open NumberedWindowInternalLiteralChildGuardEdgeProof (childGuardObservers exact_OpenChildGuardLeastInstalled)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (fullAuxiliaryDecorator childGuardedLeast)
open NumberedWindowInternalLiteralEnrichedCanonicalChildProof (exact_OpenEnrichedCanonicalChild)
open NumberedWindowInternalLiteralStrictSealedWindowProof (strictSealedWindow)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalLiteralSealedWindowProof (exact_OpenSealedWindow)
open NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof (windowRename)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem renameWindow {β : Type} (W : Program 3) (ctx ty seed : OTerm α) (j : α → β) :
    (windowAt W ctx ty seed).relabel j = windowAt W (ctx.relabel j) (ty.relabel j) (seed.relabel j) :=
  windowRename W ctx ty seed j

private theorem renameFinite {β : Type} (finite : List Nat) (ty : OTerm α) (j : α → β) :
    (literalMembership finite ty).relabel j = literalMembership finite (ty.relabel j) := by
  simp only [literalMembership,graphRename,numeralRename]

/-- Actual strict typing and coverage alone select the child’s real
minimum on the new edge. Its finite canonical scalar and the original
child guard layers are derived in the same object context. -/
theorem exact_OpenChooseStrictCanonicalChild (cv tv : Program 1) (C : Program 3)
    (baseE : Program 4) (s : Settings) (base : Program 2) (T : Program 1)
    (finite : List Nat) (ctx ty q : OTerm α) (goal : Formula α) :
    let E := withObservers baseE childGuardObservers
    let W := strictSealedWindow C s base T
    let L₀ := packedLeastOn C E s
    let L := guardedLeast (headerLeast (fullAuxiliaryDecorator L₀))
    let i := finiteScalar (addressScalar cv tv W L) finite
    WindowEndpoints W E → Preserves E L₀ →
    D B Γ (unary cv (suc z) ctx) → D B Γ (unary tv (suc z) ty) →
    D B Γ (literalMembership finite ty) → D B Γ (windowAt W ctx ty q) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (k : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (leastOnGraph C E s (ctx.relabel j) (ty.relabel j) (q.relabel j) k) →
      D B Δ (programGraph (childGuardedLeast L₀) (suc k)
        ![ctx.relabel j,ty.relabel j,q.relabel j]) →
      D B Δ (unary i (suc z) (literalAddress (ctx.relabel j) (ty.relabel j) k)) →
      D B Δ (goal.relabel j)) → D B Γ goal := by
  intro E W L₀ L i ends stable gc gt finiteType win next
  have coverage := ((exact_OpenSealedWindow C s (strictAuxWindow base T) ctx ty q).1 win).2
  have found := exact_OpenLeastOnFromCoverage C E s ctx ty q coverage
  apply casesLeastOn C E s ctx ty q goal found
  intro β j Δ k keep least
  have cvt := renameInto gc j Δ keep
  rw [unaryRename,sucRelabel,zRelabel] at cvt
  have tvt := renameInto gt j Δ keep
  rw [unaryRename,sucRelabel,zRelabel] at tvt
  have test := renameInto finiteType j Δ keep
  rw [renameFinite] at test
  have typed := renameInto win j Δ keep
  rw [renameWindow] at typed
  let c := ctx.relabel j
  let t := ty.relabel j
  let a := q.relabel j
  have child := exact_OpenChildGuardLeastInstalled C baseE s c t a k least
  have addr := exact_OpenEnrichedCanonicalChild cv tv C W E s finite c t a k ends stable cvt tvt test typed least
  exact next β j Δ k keep least child addr

#print axioms exact_OpenChooseStrictCanonicalChild
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictChildSelectionProof
