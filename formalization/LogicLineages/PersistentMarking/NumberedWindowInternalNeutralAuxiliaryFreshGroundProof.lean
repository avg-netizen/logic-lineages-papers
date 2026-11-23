module
public import LogicLineages.PersistentMarking.NumberedWindowInternalGroundFreshTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryBareFreeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementReinstallTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryFreshGroundProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialElimination)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalProbeTargets (OTerm freshAt)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalFreshProbeEmitter (chooseFresh)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalFreshProbeEmitterObjectChecks (exact_SelectedFreshOpenShape)
open NumberedWindowInternalFreshProbeParsedEmitter (selected)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof (literalNeutral neutralWithCarrier)
open NumberedWindowInternalNeutralAuxiliaryBareFreeProof (exact_OpenLiteralNeutralBareFreeI)
open NumberedWindowInternalNeutralAuxiliaryRefinement (neutralPositive)
open NumberedWindowInternalAuxBottomMembership (augmented)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA chosenH)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalAtomicMembershipSyntaxProof (membershipRename)
open NumberedWindowInternalGroundFreshTargets

/-- The original chosen fresh program supplies the exact free shape of
this u; its actual original carrier is consumed in the same literal body. -/
theorem exact_GivenLiteralNeutralFreshMembership (i : Program 1) (r : Program 3)
    (v : Inputs) (context : Nat) (α : Type) (Γ : List (Formula α)) (q u : OTerm α)
    (actual : Nonempty (Derivation (sourceBody (literalNeutral i r) context) Γ
      (freshAt (chosenA v) q u)))
    (scalar : Nonempty (Derivation (sourceBody (literalNeutral i r) context) Γ
      (carrier (literalNeutral i r) false context u))) :
    Nonempty (Derivation (sourceBody (literalNeutral i r) context) Γ (membership false u)) := by
  let S := literalNeutral i r
  let B := sourceBody S context
  let p := selected v.scalarProg v.freshBound
  have actualA : Nonempty (Derivation B Γ (freshAt (chooseFresh p) q u)) := actual
  have shape := exact_SelectedFreshOpenShape p B α Γ q u actualA
  let β := α ⊕ Fin 3
  let lift : α → β := Sum.inl
  let q' := q.relabel lift
  let u' := u.relabel lift
  let c : OTerm β := .var (.inr 0)
  let t : OTerm β := .var (.inr 1)
  let n : OTerm β := .var (.inr 2)
  let matrix := programGraph p.context c ![q'] ⊓ (programGraph p.domain t ![q'] ⊓
    (programGraph p.name n ![q'] ⊓ equal u' (packedFreeTerm c t n)))
  change Nonempty (Derivation B Γ (block matrix)) at shape
  apply actualFiniteExistentialElimination B α 3 Γ matrix (membership false u) shape
  let Δ := matrix :: Γ.map (fun A => A.relabel lift)
  have preserves : ∀ A ∈ Γ, A.relabel lift ∈ Δ :=
    fun A h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨A,h,rfl⟩)
  have carried := renameInto scalar lift Δ preserves
  rw [carrierRename] at carried
  have facts : Derivation B Δ matrix := Derivation.hypothesis List.mem_cons_self
  have e : Nonempty (Derivation B Δ (equal u' (packedFreeTerm c t n))) :=
    ⟨Derivation.conjunctionRight
      (Derivation.conjunctionRight (Derivation.conjunctionRight facts))⟩
  rw [membershipRename]
  exact exact_OpenLiteralNeutralBareFreeI i r context β Δ u' c t n e carried

/-- Ground-domain fresh-variable C in the same chosen literal even body.
The previously verified alignment yields the carrier of the actual given u. -/
theorem exact_LiteralNeutralGroundFresh (xs : Entries) (s : Settings) (W : List ProbeTy)
    (i : Program 1) (r : Program 3) (v : Inputs)
    (context : Nat)
    (pack : TupleAt xs s W i (jRaw i) (augmented i (neutralWithCarrier i r))
      (dCore i (augmented i (neutralWithCarrier i r)) permutation) v) :
    GroundFreshAt (literalNeutral i r) v.applicationGuard (chosenH v W) (chosenA v) context := by
  intro τ α Γ q u typed fresh
  obtain ⟨_,_,_,_,_,_,_,_,_,_,aligned⟩ := pack
  obtain ⟨known⟩ := aligned context .ground τ α Γ q u typed fresh
  exact exact_GivenLiteralNeutralFreshMembership i r v context α Γ q u fresh
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight known)⟩

#print axioms exact_GivenLiteralNeutralFreshMembership
#print axioms exact_LiteralNeutralGroundFresh
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryFreshGroundProof
