module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardedComputabilityProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementReinstallTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalProbeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankFreshProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open LogicLineages.OrdinalComparison.Source (Ty)
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialElimination)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalProbeTargets (OTerm freshAt FreshVariablesComputable)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA chosenH)
open NumberedWindowInternalFreshProbeParsedEmitter (selected)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeEmitter (chooseFresh)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalFreshProbeEmitterObjectChecks (exact_SelectedFreshOpenShape)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowComputabilityFormulaTargets (formula)
open NumberedWindowTypeApplicationRuleChecks (exact_FormulaSubstitution)
open NumberedWindowInternalNeutralAddressRank (addressRank)
open NumberedWindowInternalNeutralRankGuard (rankEven rankApplication)
open NumberedWindowInternalNeutralRankGuardedComputabilityProof (exact_OpenRankGuardedBareFreeC)

private theorem renameC {α β : Type} (p : Program 3) (τ : Ty) (q : OTerm α) (j : α → β) :
    (formula p τ q).relabel j = formula p τ (q.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (formula p τ q).subst (fun x => emb (.var (j x))) = _
  rw [exact_FormulaSubstitution p τ α β q _, ← termRelabelAsSubst]

/-- A genuine selected fresh report and true same-body carrier prove C
for this precise new bare free u, at every finite requested type. -/
theorem exact_OpenRankGuardedFreshC (i j raw : Program 1) (r d p : Program 3)
    (v : Inputs) (context : Nat) (τ : Ty) (α : Type) (Γ : List (Formula α)) (q u : OTerm α) :
    let g := addressRank raw
    let S := data i j (rankEven i g r) d
    let B := sourceBody S context
    Nonempty (Derivation B Γ (freshAt (chosenA v) q u)) →
    Nonempty (Derivation B Γ (carrier S false context u)) →
    Nonempty (Derivation B Γ (formula (rankApplication i g p) τ u)) := by
  intro g S B actual scalar
  let sel := selected v.scalarProg v.freshBound
  have proofA : Nonempty (Derivation B Γ (freshAt (chooseFresh sel) q u)) := actual
  have shape := exact_SelectedFreshOpenShape sel B α Γ q u proofA
  let β := α ⊕ Fin 3
  let lift : α → β := Sum.inl
  let q' := q.relabel lift
  let u' := u.relabel lift
  let ctx : OTerm β := .var (.inr 0)
  let ty : OTerm β := .var (.inr 1)
  let name : OTerm β := .var (.inr 2)
  let M := programGraph sel.context ctx ![q'] ⊓ (programGraph sel.domain ty ![q'] ⊓
    (programGraph sel.name name ![q'] ⊓ equal u' (packedFreeTerm ctx ty name)))
  change Nonempty (Derivation B Γ (block M)) at shape
  apply actualFiniteExistentialElimination B α 3 Γ M (formula (rankApplication i g p) τ u) shape
  let Δ := M :: Γ.map (fun A => A.relabel lift)
  have keep : ∀ A ∈ Γ, A.relabel lift ∈ Δ :=
    fun A h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨A,h,rfl⟩)
  have carried := renameInto scalar lift Δ keep
  rw [carrierRename] at carried
  have facts : Derivation B Δ M := Derivation.hypothesis List.mem_cons_self
  have ef : Nonempty (Derivation B Δ (equal u' (packedFreeTerm ctx ty name))) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight facts))⟩
  rw [renameC]
  exact exact_OpenRankGuardedBareFreeC i j raw r d p context τ β Δ u' ctx ty name ef carried

/-- All actual typed fresh arguments are computable using the genuine
carriers of the same newly selected tuple. No previous h is reused. -/
theorem exact_RankGuardedTypedFresh (xs : Entries) (s : Settings) (W : List ProbeTy)
    (i j raw : Program 1) (r d p : Program 3) (v : Inputs) (context : Nat)
    (pack : TupleAt xs s W i j (rankEven i (addressRank raw) r) d v)
    (pdef : v.applicationGuard = rankApplication i (addressRank raw) p) :
    FreshVariablesComputable (data i j (rankEven i (addressRank raw) r) d) v.applicationGuard
      (chosenH v W) (chosenA v) context := by
  intro σ τ α Γ q u typed fresh
  obtain ⟨_,_,_,_,_,_,_,_,_,_,aligned⟩ := pack
  obtain ⟨known⟩ := aligned context σ τ α Γ q u typed fresh
  rw [pdef]
  exact exact_OpenRankGuardedFreshC i j raw r d p v context σ α Γ q u fresh
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight known)⟩

#print axioms exact_OpenRankGuardedFreshC
#print axioms exact_RankGuardedTypedFresh
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankFreshProof
