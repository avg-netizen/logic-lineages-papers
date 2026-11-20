module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchCodeProof
import LogicLineages.PersistentMarking.NumberedWindowNumeralGraphChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchObjectGraphProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceBranchProof
  (zeroBranchIntro zeroBranchElim successorBranchIntro successorBranchElim)
open ID1Completion.InternalFixedWindowVertexDispatchSupportProof (constantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open NumberedWindowInternalProbeTargets (OTerm typeCode)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeDispatchProgram
open NumberedWindowInternalFreshProbeDispatchObjectTargets
open NumberedWindowInternalFreshProbeDispatchControlChecks
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compareEvaluation)
open NumberedWindowInternalFreshProbeDispatchCodeProof (exact_ProbeCodeInjective)
open NumberedWindowProbeCode (code)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem literalGraph {n : Nat} (k : Nat) (xs : Fin n → OTerm α) :
    Nonempty (Derivation body Γ (programGraph (literal n k) (numeral k) xs)) := by
  rw [exact_DispatchControlAST.2.1]
  exact constantValue n k xs

/-- Only the two closed type numerals are evaluated. q stays an
arbitrary open object term projected by the literal selected program. -/
private theorem testValue (σ τ : ProbeTy) (q : OTerm α) :
    Nonempty (Derivation body Γ (programGraph (typeTest τ)
      (numeral (if σ = τ then 1 else 0)) ![numeral (code σ),q])) := by
  let ns := code σ ::ᵥ code τ ::ᵥ nil
  have hv : evaluate compareNumbers ns = if σ = τ then 1 else 0 := by
    rw [show ns = code σ ::ᵥ code τ ::ᵥ nil from rfl,compareEvaluation]
    by_cases he : σ = τ
    · subst τ
      simp
    · have hn : code σ ≠ code τ := fun h => he (exact_ProbeCodeInjective h)
      simp [he,hn]
  obtain ⟨h⟩ := NumberedWindowNumeralGraphChecks.exact_NumeralGraph 2 compareNumbers ns body α Γ
  rw [hv] at h
  have hinputs : (NumberedWindowNumeralGraphTargets.inputs ns : Fin 2 → OTerm α) =
      ![numeral (code σ),numeral (code τ)] := by
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i <;> rfl
  rw [hinputs] at h
  unfold typeTest
  apply compositionValue compareNumbers _ _ _ ![numeral (code σ),numeral (code τ)] ⟨h⟩
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i
  · exact projectionValue (0 : Fin 2) ![numeral (code σ),q]
  · exact literalGraph (code τ) ![numeral (code σ),q]

private theorem hitValue (τ : ProbeTy) (q : OTerm α) :
    Nonempty (Derivation body Γ (programGraph (typeTest τ) (numeral 1) ![numeral (typeCode τ),q])) := by
  simpa only [if_pos rfl,exact_DispatchObjectTypeCode] using
    (testValue (body := body) (Γ := Γ) τ τ q)

private theorem missValue (σ τ : ProbeTy) (q : OTerm α) (h : σ ≠ τ) :
    Nonempty (Derivation body Γ (programGraph (typeTest τ) z ![numeral (typeCode σ),q])) := by
  simpa only [if_neg h,exact_DispatchObjectTypeCode] using
    (testValue (body := body) (Γ := Γ) σ τ q)

private theorem liftIntro (l : Leaves) (τ : ProbeTy) (out t q : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (verify l τ) out ![q]))) :
    Nonempty (Derivation body Γ (programGraph (liftBranch l τ) out ![t,q])) := by
  unfold liftBranch
  apply compositionValue (verify l τ) _ out ![t,q] ![q] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue (1 : Fin 2) ![t,q]

private theorem liftElim (l : Leaves) (τ : ProbeTy) (out t q : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (liftBranch l τ) out ![t,q]))) :
    Nonempty (Derivation body Γ (programGraph (verify l τ) out ![q])) := by
  apply compositionRecover (verify l τ) (Fin.cons (Program.projection (1 : Fin 2)) Fin.elim0)
    out ![t,q] ![q] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue (1 : Fin 2) ![t,q]

/-- Meta-level transportation of actual open derivations, in both
directions, for exactly this selected dispatch and this selected branch. -/
theorem memberAt (l : Leaves) (W : List ProbeTy) (τ : ProbeTy) (hm : τ ∈ W) (out q : OTerm α) :
    Nonempty (Derivation body Γ (programGraph (dispatch l W) out ![numeral (typeCode τ),q])) ↔
    Nonempty (Derivation body Γ (programGraph (verify l τ) out ![q])) := by
  induction W with
  | nil => cases hm
  | cons σ W ih =>
    let xs : Fin 2 → OTerm α := ![numeral (typeCode τ),q]
    change Nonempty (Derivation body Γ
      (programGraph (chooseBranch (typeTest σ) (dispatch l W) (liftBranch l σ)) out xs)) ↔ _
    rw [exact_DispatchControlAST.2.2.2.2.1]
    by_cases he : τ = σ
    · subst σ
      have htest : Nonempty (Derivation body Γ (programGraph (typeTest τ) (numeral 1) xs)) := hitValue τ q
      constructor
      · intro hd
        exact liftElim l τ out (numeral (typeCode τ)) q
          (successorBranchElim (typeTest τ) (dispatch l W) (liftBranch l τ) out z xs htest hd)
      · intro hb
        exact successorBranchIntro (typeTest τ) (dispatch l W) (liftBranch l τ) out z xs htest
          (liftIntro l τ out (numeral (typeCode τ)) q hb)
    · have htail : τ ∈ W := (List.mem_cons.mp hm).resolve_left he
      have htest : Nonempty (Derivation body Γ (programGraph (typeTest σ) z xs)) :=
        missValue τ σ q he
      constructor
      · intro hd
        exact (ih htail).mp (zeroBranchElim (typeTest σ) (dispatch l W) (liftBranch l σ) out xs htest hd)
      · intro hv
        exact zeroBranchIntro (typeTest σ) (dispatch l W) (liftBranch l σ) out xs htest ((ih htail).mpr hv)

theorem dispatchGraph : ExactProbeDispatchGraph := by
  intro l W τ hm body α Γ out q
  let H := programGraph (dispatch l W) out ![numeral (typeCode τ),q]
  let B := programGraph (verify l τ) out ![q]
  have hf : Nonempty (Derivation body (H :: Γ) B) :=
    (memberAt l W τ hm out q).mp ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hb : Nonempty (Derivation body (B :: Γ) H) :=
    (memberAt l W τ hm out q).mpr ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem dispatchReject : ExactProbeDispatchReject := by
  intro l W τ hn body α Γ q
  induction W with
  | nil =>
    change Nonempty (Derivation body Γ
      (programGraph (zeroAt 2) z ![numeral (typeCode τ),q]))
    rw [exact_DispatchControlAST.1]
    exact constantZeroValue _
  | cons σ W ih =>
    have he : τ ≠ σ := fun h => hn (List.mem_cons.mpr (Or.inl h))
    have htail : τ ∉ W := fun h => hn (List.mem_cons_of_mem _ h)
    let xs : Fin 2 → OTerm α := ![numeral (typeCode τ),q]
    change Nonempty (Derivation body Γ
      (programGraph (chooseBranch (typeTest σ) (dispatch l W) (liftBranch l σ)) z xs))
    rw [exact_DispatchControlAST.2.2.2.2.1]
    exact zeroBranchIntro (typeTest σ) (dispatch l W) (liftBranch l σ) z xs
      (missValue τ σ q he) (ih htail)

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchObjectGraphProof
