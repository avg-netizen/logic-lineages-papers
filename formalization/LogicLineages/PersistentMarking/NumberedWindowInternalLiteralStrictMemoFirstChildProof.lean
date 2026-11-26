module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMemoChildFromForkProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMemoFirstChildProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.SourcePresentation (Data sourceBody)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons unary)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalOriginalFirstHopCoreProof (literalAddress)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (D finiteScalar)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn)
open NumberedWindowInternalLiteralLeastOnFixedPointProof (WindowEndpoints)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalLiteralStrictDualChildProof (strictDualRaw)
open NumberedWindowInternalLiteralStrictSealedWindowProof (strictSealedWindow)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof (memoFilteredLeast MemoSelectedReports)
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalLiteralStrictDualInversionForkProof (exact_OpenStrictDualNeutralInversionFromChild)
open NumberedWindowInternalLiteralStrictMemoChildFromForkProof (exact_OpenStrictMemoChildFromFork)
open NumberedWindowInternalNeutralFactsTargets (direct directData atom)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource)
open NumberedWindowInternalAtomicRefinement (bottomSource)

attribute [local irreducible] programGraph recursiveTypedMemo packedLeastOn
variable {α : Type} {Γ : List (Formula α)}

def directChildExists {α : Type} (S : Data) (h : Program 3) (c : Nat) (x : OTerm α) : Formula α :=
  existsOne (direct S h c (x.relabel Sum.inl) (.var (.inr 0)))

private theorem directRename {β : Type} (S : Data) (h : Program 3) (c : Nat) (x y : OTerm α) (j : α → β) :
    (direct S h c x y).relabel j = direct S h c (x.relabel j) (y.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (direct S h c x y).subst (fun a => emb (.var (j a))) = _
  simp only [direct,edgeSubst,← termRelabelAsSubst]

theorem exact_DirectChildExistsRename {β : Type} (S : Data) (h : Program 3) (c : Nat)
    (x : OTerm α) (j : α → β) :
    (directChildExists S h c x).relabel j = directChildExists S h c (x.relabel j) := by
  unfold directChildExists
  rw [existsRename,directRename]
  simp only [Term.relabel_relabel]
  rfl

theorem exact_DirectChildExistsIntro (S : Data) (h : Program 3) (c : Nat)
    (x y : OTerm α) (step : D (sourceBody S c) Γ (direct S h c x y)) :
    D (sourceBody S c) Γ (directChildExists S h c x) := by
  unfold directChildExists
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb y)
  simpa only [instantiate,bindEmbedding,direct,edgeSubst,liftBind,varBind] using Classical.choice step

/-- Full extraction of the original function's genuine direct child
from a genuine accepted neutral application and its genuine direct hop.
Bottom is the exact other alternative. This does not yet identify the
application of that child at the ultimate result address. -/
theorem exact_OpenStrictMemoInversionFirstChild
    (cv tv : Program 1) (C : Program 3) (Base : Program 4) (X : Program 2) (s : Settings)
    (leaf : Nat → Program 3) (other : Program 3) (rawBase base : Program 2) (rawT V T : Program 1)
    (finite : List Nat) (c : Nat) (x u t y : OTerm α) :
    let E := recursiveTypedMemo Base
    let L₀ := packedLeastOn C E s
    let L := memoFilteredLeast C Base s
    let W := strictSealedWindow C s base T
    let i := finiteScalar (addressScalar cv tv W L) finite
    let raw := guardedRaw (strictDualRaw C s leaf other rawBase base rawT V T)
    let R := rawWithTarget i cv tv raw L
    let data := S i cv tv R L
    let B := sourceBody data c
    WindowEndpoints W E → Preserves E L₀ → MemoSelectedReports C s Base →
    D B Γ (atom neutralSource x) →
    D B Γ (programGraph (applicationGuard i L) (suc z) ![x,u,t]) →
    D B Γ (direct data (hop cv tv R L) c t y) →
    D B Γ (atom bottomSource y ⊔ directChildExists data (hop cv tv R L) c x) := by
  intro E L₀ L W i raw R data B ends stable selected neutral app step
  let goal := directChildExists data (hop cv tv R L) c x
  apply exact_OpenStrictDualNeutralInversionFromChild C X s leaf other rawBase base rawT V T i cv tv L₀ c
    x u t y goal neutral app step
  intro β j Δ ctx result dom cod fn arg k sc st before after cert q w r d e f a child d' e' g a'
    keep left right parsed address context _ _ parent parts rawFacts windows calls
  obtain ⟨rawFacts⟩ := rawFacts
  obtain ⟨windows⟩ := windows
  rw [exact_DirectChildExistsRename] 
  apply exact_OpenStrictMemoChildFromFork cv tv C Base s base T raw finite c
    (x.relabel j) (u.relabel j) ctx result dom cod fn arg sc st before after cert q w r d e f a child g
    (directChildExists data (hop cv tv R L) c (x.relabel j)) ends stable selected left right parsed context
    parent parts.source ⟨Derivation.conjunctionLeft rawFacts⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight windows)⟩ calls
  intro γ n Θ m stay _ _ generated
  rw [exact_DirectChildExistsRename]
  exact exact_DirectChildExistsIntro data (hop cv tv R L) c ((x.relabel j).relabel n)
    (literalAddress (sc.relabel n) (rawCons (d.relabel n) (e.relabel n)) m) generated

#print axioms exact_DirectChildExistsRename
#print axioms exact_DirectChildExistsIntro
#print axioms exact_OpenStrictMemoInversionFirstChild
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMemoFirstChildProof
