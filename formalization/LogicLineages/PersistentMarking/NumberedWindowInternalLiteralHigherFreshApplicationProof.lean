module
public import LogicLineages.PersistentMarking.NumberedWindowInternalTypedNeutralEndpointCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedScalarTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeReinstallTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHigherFreshApplicationProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialElimination)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalProbeTargets (OTerm typeCode typedAt freshAt)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA chosenH)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressReports arrowReports sourceShape)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks (exact_OpenLiteralParsedFresh)
open NumberedWindowInternalAtomicApplicationShapeObjectChecks (exact_OpenAtomicApplicationShape)
open NumberedWindowInternalAtomicApplicationShapeObjectTargets (freeTerm literalApplicationShape)
open NumberedWindowInternalAtomicApplicationShapeReinstallTargets (refineInputs)
open NumberedWindowInternalPullbackSyntaxProof (acceptsRename)
open NumberedWindowInternalLiteralRefinedScalarTargets (refinedLiteral)
open NumberedWindowComputabilityFormulaTargets (accepts)

/-- Expose a genuine neutral application with a selected **higher-type**
fresh head. Its source typing is for the reselected h which executes
the same p. Given an actual call of p on that exact u, leave the exact
higher type and raw-context/name shape visible for the later neutral cut.
No accepted endpoint is asserted computable or itself typed by h. -/
theorem exact_OpenLiteralHigherFreshApplication (i : Program 1) (r : Program 3) (c : Nat)
    (v : Inputs) (W : List ProbeTy) (σ τ ω : ProbeTy) (α : Type) (Γ : List (Formula α))
    (q u arg out : OTerm α) (goal : Formula α)
    (typed : Nonempty (Derivation (sourceBody (refinedLiteral i r) c) Γ
      (typedAt (chosenH (refineInputs v) W) (.arrow (.arrow σ τ) ω) q)))
    (fresh : Nonempty (Derivation (sourceBody (refinedLiteral i r) c) Γ (freshAt (chosenA (refineInputs v)) q u)))
    (app : Nonempty (Derivation (sourceBody (refinedLiteral i r) c) Γ
      (accepts (refineInputs v).applicationGuard u arg out)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (ctx d name : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation (sourceBody (refinedLiteral i r) c) Δ
        (equal d (numeral (typeCode (.arrow σ τ))))) →
      Nonempty (Derivation (sourceBody (refinedLiteral i r) c) Δ (equal (u.relabel j) (packedFreeTerm ctx d name))) →
      Nonempty (Derivation (sourceBody (refinedLiteral i r) c) Δ
        (literalApplicationShape ctx d (freeTerm d name) (arg.relabel j) (out.relabel j))) →
      Nonempty (Derivation (sourceBody (refinedLiteral i r) c) Δ (goal.relabel j))) :
    Nonempty (Derivation (sourceBody (refinedLiteral i r) c) Γ goal) := by
  let S := refinedLiteral i r
  let B := sourceBody S c
  let h := refineInputs v
  let β := α ⊕ Fin 6
  let j : α → β := Sum.inl
  let ctx : OTerm β := .var (.inr 0)
  let res : OTerm β := .var (.inr 1)
  let d : OTerm β := .var (.inr 2)
  let e : OTerm β := .var (.inr 3)
  let raw : OTerm β := .var (.inr 4)
  let name : OTerm β := .var (.inr 5)
  let q' := q.relabel j
  let u' := u.relabel j
  let matrix := addressReports q' ctx res raw ⊓ (arrowReports q' d e ⊓
    (sourceShape q' ctx res d e raw ⊓ (programGraph h.freshBound name ![raw] ⊓
      (equal u' (packedFreeTerm ctx d name) ⊓
        (equal d (numeral (typeCode (.arrow σ τ))) ⊓ equal e (numeral (typeCode ω)))))))
  have seen := exact_OpenLiteralParsedFresh h W (.arrow σ τ) ω B α Γ q u typed fresh
  apply actualFiniteExistentialElimination B α 6 Γ matrix goal seen
  let Δ := matrix :: Γ.map (fun f => f.relabel j)
  have keep : ∀ f ∈ Γ, f.relabel j ∈ Δ :=
    fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have a := renameInto app j Δ keep
  rw [acceptsRename] at a
  have facts : Derivation B Δ matrix := Derivation.hypothesis List.mem_cons_self
  have tail := Derivation.conjunctionRight (Derivation.conjunctionRight
    (Derivation.conjunctionRight (Derivation.conjunctionRight facts)))
  have hFree := Derivation.conjunctionLeft tail
  have hTy := Derivation.conjunctionLeft (Derivation.conjunctionRight tail)
  have applied := exact_OpenAtomicApplicationShape.1 v.applicationGuard B β Δ u'
    (arg.relabel j) (out.relabel j) ctx d name ⟨hFree⟩ a
  exact next β j Δ ctx d name keep ⟨hTy⟩ ⟨hFree⟩ applied

#print axioms exact_OpenLiteralHigherFreshApplication
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHigherFreshApplicationProof
