module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAddressedGuardedPushProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedForwardBindingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationWitnessProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteScalarGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundLeastTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressThinDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationRebuildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalChildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastFixedPointProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSelectedChildWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectSelectorsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPushedForwardImageProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalComputabilityDownwardSyntaxProof (edgeRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.SourcePresentation (Data sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof (windowRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalOriginalFirstHopCoreProof (literalAddress exact_OriginalLiteralAddressReport)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (addressReportRename)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralPositiveEndpointGuardProof (positiveEndpointGuard)
open NumberedWindowInternalLiteralAddressedGuardedPushProof (exact_OpenGuardedPositiveFromFold)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (D finiteScalar exact_MakeLiteralFiniteScalar)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalLiteralRoundLeastTargets (SameLeastOnEdge)
open NumberedWindowInternalLiteralLeastFixedPointProof (exact_LiteralLeastFixedPointFromEdge)
open NumberedWindowInternalLiteralSelectedChildWindowProof (exact_OpenLiteralSelectedWindow)
open NumberedWindowInternalLiteralCanonicalChildProof (exact_OpenLiteralScalarFromSelfLeast)
open NumberedWindowInternalLiteralApplicationRebuildProof (exact_OpenLiteralApplicationFromReportedLeast)
open NumberedWindowInternalLiteralApplicationWitnessProof (exact_OpenLiteralForwardImageWitness)
open NumberedWindowInternalPullbackTargets (forwardImage)
open NumberedWindowInternalPullbackSyntaxProof (acceptsRename)
open NumberedWindowInternalThinMatchedForwardBindingProof (pushed)
open NumberedWindowInternalSparsePositiveTransitivityTargets (supplied)
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (suppliedCases suppliedRename)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem imageRename {β : Type} (data : Data) (p : Program 3) (c : Nat)
    (g u x : OTerm α) (j : α → β) :
    (forwardImage data p c g u x).relabel j =
      forwardImage data p c (g.relabel j) (u.relabel j) (x.relabel j) := by
  simp only [forwardImage,existsRename,conjunctionRename,acceptsRename,edgeRename,Term.relabel_relabel,Term.relabel]
  rfl

private theorem finiteRename {β : Type} (types : List Nat) (ty : OTerm α) (j : α → β) :
    (literalMembership types ty).relabel j = literalMembership types (ty.relabel j) := by
  simp only [literalMembership,graphRename,numeralRename]

theorem exact_OpenPlainFiniteScalarAtLeast (cv tv : Program 1) (C W : Program 3) (X : Program 2)
    (s : Settings) (paid : SameLeastOnEdge C X W s) (types : List Nat) (ctx ty seed k : OTerm α) :
    let L := packedLeastProgram C X W s
    let i := finiteScalar (addressScalar cv tv W L) types
    D B Γ (unary cv (suc z) ctx) → D B Γ (unary tv (suc z) ty) →
    D B Γ (literalMembership types ty) → D B Γ (windowAt W ctx ty seed) →
    D B Γ (leastGraph C X W s ctx ty seed k) → D B Γ (unary i (suc z) (literalAddress ctx ty k)) := by
  intro L i gc gt listed win least
  have fixed := exact_LiteralLeastFixedPointFromEdge C X W s paid ctx ty seed k least
  have selected := exact_OpenLiteralSelectedWindow C X W s ctx ty seed k win least
  have scalar := exact_OpenLiteralScalarFromSelfLeast cv tv W L ctx ty k gc gt selected fixed
  obtain ⟨_,_,typeRead,_⟩ := NumberedWindowInternalAtomicRefinementObjectSelectorsProof.literalAddress
    (body := B) (Γ := Γ) ctx ty k
  exact exact_MakeLiteralFiniteScalar (addressScalar cv tv W L) types (literalAddress ctx ty k) ty typeRead scalar listed

/-- Assemble the actual forward image from a physically lifted path.
This closes the output boundary without treating scalar canonicality
or the reconstructed application as consequences of numeric fit. -/
theorem exact_OpenForwardImageFromPushed (cv tv : Program 1) (C W : Program 3) (X : Program 2)
    (s : Settings) (raw : Program 5) (paid : SameLeastOnEdge C X W s) (types : List Nat)
    (c : Nat) (g u x ctx dom cod fn arg earlier : OTerm α) :
    let L := packedLeastProgram C X W s
    let i := finiteScalar (addressScalar cv tv W L) types
    let data := literalData i (positiveEndpointGuard i (addressPositive cv tv raw L))
    let B := sourceBody data c
    let parent := auxiliaryTerm dom cod fn arg
    let p := applicationGuard i L
    D B Γ (unary cv (suc z) ctx) → D B Γ (unary tv (suc z) cod) →
    D B Γ (literalMembership types cod) → D B Γ (windowAt W ctx cod parent) →
    D B Γ (addressReport g ctx (rawCons dom cod) fn) → D B Γ (unary i (suc z) g) →
    D B Γ (addressReport u ctx dom arg) → D B Γ (unary i (suc z) u) →
    D B Γ (addressReport x ctx cod earlier) → D B Γ (unary i (suc z) x) →
    D B Γ (pushed C X W s raw ctx cod parent earlier) →
    D B Γ (forwardImage data p c g u x) := by
  intro L i data B parent p gc gt listed formed fg gs aa us old xs lifted
  let j : α → α ⊕ Fin 1 := Sum.inl
  let later : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let row := leastGraph C X W s (ctx.relabel j) (cod.relabel j) (parent.relabel j) later ⊓
    supplied raw L (ctx.relabel j) (cod.relabel j) (earlier.relabel j) later
  let Δ := row :: Γ.map weaken
  have keep (φ : Formula α) (h : φ ∈ Γ) : φ.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨φ,h,rfl⟩)
  have chosen : Derivation B Δ row := Derivation.hypothesis List.mem_cons_self
  let ca := ctx.relabel j
  let d := dom.relabel j
  let t := cod.relabel j
  let f := fn.relabel j
  let a := arg.relabel j
  let y := literalAddress ca t later
  have hgc := renameInto gc j Δ keep
  have hgt := renameInto gt j Δ keep
  have listed' := renameInto listed j Δ keep
  have window := renameInto formed j Δ keep
  have fga := renameInto fg j Δ keep
  have gs' := renameInto gs j Δ keep
  have ar := renameInto aa j Δ keep
  have us' := renameInto us j Δ keep
  have xr := renameInto old j Δ keep
  have xs' := renameInto xs j Δ keep
  rw [unaryRename,sucRelabel,zRelabel] at hgc hgt gs' us' xs'
  rw [finiteRename] at listed'
  change D B Δ ((NumberedWindowInternalAuxWindowOpenTargets.windowGraph W ctx cod parent).relabel j) at window
  rw [windowRename,auxiliaryRename] at window
  rw [addressReportRename,rawConsRename] at fga
  rw [addressReportRename] at ar xr
  have found : D B Δ (leastGraph C X W s ca t (auxiliaryTerm d t f a) later) := by
    have original : D B Δ (leastGraph C X W s ca t (parent.relabel j) later) := ⟨Derivation.conjunctionLeft chosen⟩
    rwa [auxiliaryRename] at original
  have sy := exact_OpenPlainFiniteScalarAtLeast cv tv C W X s paid types ca t _ later hgc hgt listed' window found
  have app := exact_OpenLiteralApplicationFromReportedLeast i L (g.relabel j) (u.relabel j) y ca d t f a later
    fga ar gs' us' found ⟨refl y⟩
  have endReport := exact_OriginalLiteralAddressReport (B := B) (Γ := Δ) ca t later
  have after : D B Δ (forwardImage data p c (g.relabel j) (u.relabel j) (x.relabel j)) := by
    apply suppliedCases raw L ca t (earlier.relabel j) later _
      ⟨Derivation.conjunctionRight chosen⟩
    intro γ k Θ cert stay path
    rw [imageRename]
    have cr := renameInto xr k Θ stay
    have nr := renameInto endReport k Θ stay
    rw [addressReportRename] at cr nr
    have cx := renameInto hgc k Θ stay
    have tx := renameInto hgt k Θ stay
    have iOld := renameInto xs' k Θ stay
    have iNew := renameInto sy k Θ stay
    rw [unaryRename,sucRelabel,zRelabel] at cx tx iOld iNew
    have prog := renameInto app k Θ stay
    simp only [ID1Completion.InternalControlGraphSupportProof.programRename,
      NumberedWindowInternalSparseFieldParserOpenSyntaxProof.tripleInputsRename,sucRelabel,zRelabel] at prog
    have e := exact_OpenGuardedPositiveFromFold i cv tv raw L c
      ((x.relabel j).relabel k) (y.relabel k) (ca.relabel k) (t.relabel k)
      ((earlier.relabel j).relabel k) (later.relabel k) cert cr nr cx tx iOld iNew path
    have application : D B Θ (NumberedWindowComputabilityFormulaTargets.accepts p
        ((g.relabel j).relabel k) ((u.relabel j).relabel k) (y.relabel k)) := by
      unfold NumberedWindowComputabilityFormulaTargets.accepts programGraph at *
      exact prog
    exact exact_OpenLiteralForwardImageWitness data p c ((g.relabel j).relabel k)
      ((u.relabel j).relabel k) ((x.relabel j).relabel k) (y.relabel k) application e
  obtain ⟨done⟩ := after
  obtain ⟨report⟩ := lifted
  have final : Derivation B Δ (weaken (forwardImage data p c g u x)) := by
    change Derivation B Δ ((forwardImage data p c g u x).relabel j)
    rwa [imageRename]
  exact ⟨Derivation.existentialElimination report final⟩

#print axioms imageRename
#print axioms exact_OpenPlainFiniteScalarAtLeast
#print axioms exact_OpenForwardImageFromPushed
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPushedForwardImageProof
