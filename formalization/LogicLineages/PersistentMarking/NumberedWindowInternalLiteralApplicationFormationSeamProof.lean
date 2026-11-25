module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationSelectedCarrierProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationNeutralOutputProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationFormationSeamProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (existsOne)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof (inputsRename)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseApplicationFrontendOpenForwardProof (forward)
open NumberedWindowInternalSparseApplicationFrontendOpenBindingProof (rowCases)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open NumberedWindowInternalLiteralRoundLeastTargets (SameLeastOnEdge)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S)
open NumberedWindowInternalLiteralApplicationSelectedCarrierProof (exact_OpenLiteralApplicationCarrierAtSelected)
open NumberedWindowInternalLiteralApplicationNeutralOutputProof (exact_OpenLiteralApplicationNeutralOutput)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource)
open NumberedWindowInternalNeutralFactsTargets (atom)

attribute [local irreducible] programGraph
variable {α : Type} {Γ : List (Formula α)}

/-- The exact remaining formation obligation in application closure:
from the actual accepted scalar inputs and their parsed coordinates,
show the two validators and the actual window of the constructed seed.
The selected guarded least report is retained as a premise, rather
than starting with a stronger assumption about arbitrary auxiliaries. -/
@[expose] def SelectedSeedFormation (i cv tv : Program 1) (W L : Program 3) : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (f u ctx r dom cod fn arg k : OTerm α),
    D B Γ (unary i (suc z) f) → D B Γ (unary i (suc z) u) →
    D B Γ (parsedApplicationInputs f u ctx r dom cod fn arg) →
    D B Γ (programGraph L (suc k) ![ctx,cod,auxiliaryTerm dom cod fn arg]) →
    D B Γ (unary cv (suc z) ctx) ∧ D B Γ (unary tv (suc z) cod) ∧
    D B Γ (windowAt W ctx cod (auxiliaryTerm dom cod fn arg))

private theorem carrierFromReport (cv tv : Program 1)
    (C W : Program 3) (X : Program 2) (s : Settings) (paid : SameLeastOnEdge C X W s)
    (raw : Program 5) (c : Nat) (f u y ctx r dom cod fn arg : OTerm α) :
    let L := guardedLeast (headerLeast (packedLeastProgram C X W s))
    let i := addressScalar cv tv W L
    let R := rawWithTarget i cv tv (guardedRaw raw) L
    let data := S i cv tv R L
    let B := sourceBody data c
    SelectedSeedFormation i cv tv W L →
    D B Γ (unary i (suc z) f) → D B Γ (unary i (suc z) u) →
    D B Γ (parsedApplicationInputs f u ctx r dom cod fn arg) →
    D B Γ (outputReport L ctx cod (auxiliaryTerm dom cod fn arg) y) →
    D B Γ (carrier data false c y) := by
  intro L i R data B form left right inputs out
  let j : α → α ⊕ Fin 1 := Sum.inl
  let k : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let A := programGraph L (suc k) ![ctx.relabel j,cod.relabel j,(auxiliaryTerm dom cod fn arg).relabel j] ⊓
    eqn (y.relabel j) (addressTerm (ctx.relabel j) (cod.relabel j) k)
  let Δ := A :: Γ.map weaken
  have keep (φ : Formula α) (h : φ ∈ Γ) : φ.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨φ,h,rfl⟩)
  have one := renameInto left j Δ keep
  have two := renameInto right j Δ keep
  have parsed := renameInto inputs j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at one two
  rw [inputsRename] at parsed
  have row : Derivation B Δ A := Derivation.hypothesis List.mem_cons_self
  have least : D B Δ (programGraph L (suc k)
      ![ctx.relabel j,cod.relabel j,(auxiliaryTerm dom cod fn arg).relabel j]) :=
    ⟨Derivation.conjunctionLeft row⟩
  rw [auxiliaryRename] at least
  obtain ⟨gc,gt,formed⟩ := form B _ Δ (f.relabel j) (u.relabel j) (ctx.relabel j)
    (r.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) k
    one two parsed least
  have result := exact_OpenLiteralApplicationCarrierAtSelected cv tv C W X s paid raw c
    (ctx.relabel j) (cod.relabel j) _ k (y.relabel j) gc gt formed least
    ⟨Derivation.conjunctionRight row⟩
  have actual : D B Δ ((carrier data false c y).relabel j) := by
    rw [carrierRename]
    exact result
  obtain ⟨introRow⟩ := actual
  obtain ⟨opened⟩ := out
  exact ⟨Derivation.existentialElimination opened introRow⟩

/-- With exactly the actual seed milestone exposed, both conclusions
of neutral application closure are recovered on the same body and
physical application. No condition about the head is needed for
this part; it is the inversion rule that needs a neutral source. -/
theorem exact_OpenLiteralApplicationClosureFromFormation (cv tv : Program 1)
    (C W : Program 3) (X : Program 2) (s : Settings) (paid : SameLeastOnEdge C X W s)
    (raw : Program 5) (c : Nat) (f u y : OTerm α) :
    let L := guardedLeast (headerLeast (packedLeastProgram C X W s))
    let i := addressScalar cv tv W L
    let R := rawWithTarget i cv tv (guardedRaw raw) L
    let data := S i cv tv R L
    let B := sourceBody data c
    SelectedSeedFormation i cv tv W L →
    D B Γ (programGraph (applicationGuard i L) (suc z) ![f,u,y]) →
    D B Γ (carrier data false c y) ∧ D B Γ (atom neutralSource y) := by
  intro L i R data B form accepted
  refine ⟨?_,exact_OpenLiteralApplicationNeutralOutput i (packedLeastProgram C X W s) f u y accepted⟩
  obtain ⟨row⟩ := forward i L f u y accepted
  let h := Derivation.conjunctionRight row
  have left : D B Γ (unary i (suc z) f) := ⟨Derivation.conjunctionLeft row⟩
  have right : D B Γ (unary i (suc z) u) := ⟨Derivation.conjunctionLeft h⟩
  apply rowCases L f u y (carrier data false c y) ⟨Derivation.conjunctionRight h⟩
  intro β j Δ ctx r dom cod fn arg keep known
  rw [carrierRename]
  have one := renameInto left j Δ keep
  have two := renameInto right j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at one two
  obtain ⟨pair⟩ := known
  exact carrierFromReport cv tv C W X s paid raw c (f.relabel j) (u.relabel j) (y.relabel j)
    ctx r dom cod fn arg form one two ⟨Derivation.conjunctionLeft pair⟩
    ⟨Derivation.conjunctionRight pair⟩

#print axioms exact_OpenLiteralApplicationClosureFromFormation
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationFormationSeamProof
