module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictChildSelectionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictOperandMinimaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictNonAuxChildCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalOriginalFirstHopCoreProof (literalAddress)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalNeutralFactsTargets (direct)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (D finiteScalar)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralLeastOnFixedPointProof (WindowEndpoints)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralEdgeObserversProof (withObservers)
open NumberedWindowInternalLiteralChildGuardEdgeProof (childGuardObservers)
open NumberedWindowInternalLiteralStrictSealedWindowProof (strictSealedWindow)
open NumberedWindowInternalLiteralStrictChildSelectionProof (exact_OpenChooseStrictCanonicalChild)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof
  (fullAuxiliaryDecorator childGuardedLeast exact_OpenFullFilteredNonAuxLeast)
open NumberedWindowInternalLiteralCarrierChildHopProof (exact_OpenCarrierChildHopAtLeast)

attribute [local irreducible] programGraph
variable {α : Type} {Γ : List (Formula α)}

/-- For a genuine strict contextual raw child with non-auxiliary
endpoints, select the actual target from its strict domain and obtain
the literal direct certificate. The source is the already identified
child minimum of the original accepted function. -/
theorem exact_OpenStrictNonAuxChildCases (cv tv : Program 1) (C : Program 3) (baseE : Program 4)
    (s : Settings) (base : Program 2) (T : Program 1) (raw : Program 5) (finite : List Nat) (c : Nat)
    (ctx ty seed witness target source : OTerm α) (goal : Formula α) :
    let E := withObservers baseE childGuardObservers
    let W := strictSealedWindow C s base T
    let L₀ := packedLeastOn C E s
    let L := guardedLeast (headerLeast (fullAuxiliaryDecorator L₀))
    let i := finiteScalar (addressScalar cv tv W L) finite
    let R := rawWithTarget i cv tv raw L
    let data := S i cv tv R L
    let B := sourceBody data c
    WindowEndpoints W E → Preserves E L₀ →
    D B Γ (unary cv (suc z) ctx) → D B Γ (unary tv (suc z) ty) →
    D B Γ (literalMembership finite ty) → D B Γ (windowAt W ctx ty target) →
    D B Γ (unary termShape z seed) → D B Γ (unary termShape z target) →
    D B Γ (programGraph raw (suc z) ![ctx,ty,seed,witness,target]) →
    D B Γ (programGraph (childGuardedLeast L₀) (suc source) ![ctx,ty,seed]) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (k : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (leastOnGraph C E s (ctx.relabel j) (ty.relabel j) (target.relabel j) k) →
      D B Δ (unary i (suc z) (literalAddress (ctx.relabel j) (ty.relabel j) k)) →
      D B Δ (direct data (hop cv tv R L) c
        (literalAddress (ctx.relabel j) (ty.relabel j) (source.relabel j))
        (literalAddress (ctx.relabel j) (ty.relabel j) k)) → D B Δ (goal.relabel j)) →
    D B Γ goal := by
  intro E W L₀ L i R data B ends stable gc gt listed formed sourcePlain targetPlain child sourceMin use
  have left := exact_OpenFullFilteredNonAuxLeast L₀ ctx ty seed source sourcePlain sourceMin
  apply exact_OpenChooseStrictCanonicalChild cv tv C baseE s base T finite ctx ty target goal
    ends stable gc gt listed formed
  intro β j Δ k keep right childMin carrier
  have l := renameInto left j Δ keep
  simp only [programRename,tripleInputsRename,sucRelabel] at l
  have cvt := renameInto gc j Δ keep
  have tvt := renameInto gt j Δ keep
  have n := renameInto targetPlain j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at cvt tvt n
  have raw' := renameInto child j Δ keep
  simp only [NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof.graph5Rename,sucRelabel,zRelabel] at raw'
  let sc := ctx.relabel j
  let st := ty.relabel j
  let rd := target.relabel j
  have r := exact_OpenFullFilteredNonAuxLeast L₀ sc st rd k n childMin
  have one := exact_OpenCarrierChildHopAtLeast i cv tv raw L c sc st (seed.relabel j)
    (witness.relabel j) rd (source.relabel j) k cvt tvt raw' l r carrier
  exact use β j Δ k keep right carrier one

#print axioms exact_OpenStrictNonAuxChildCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictNonAuxChildCasesProof
