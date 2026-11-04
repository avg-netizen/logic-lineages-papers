module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SystemSourceTargets
public import LogicLineages.OrdinalComparison.SourceSignedPairProof
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorProof
public import LogicLineages.OrdinalComparison.SourceAggregateCompletionProof
public import LogicLineages.OrdinalComparison.SourceGroundEquivalenceProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SystemProof
open OriginalDomain FunctionalDetector SourceCollisionCompletion
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem valuation_preserves {Γ Δ : List Ty} (r : Renaming Γ Δ)
    (ρ : AdmissibleSubstitution Γ) (σ : AdmissibleSubstitution Δ) (h : Preserves r ρ σ) :
    (fun c => valuation σ (ordinalComponentRename r c)) = valuation ρ := by
  funext c
  rcases c with ⟨τ,x,j⟩
  exact congrArg closedValue (h τ x j)

theorem expression_preserves {Γ Δ : List Ty} (r : Renaming Γ Δ)
    (ρ : AdmissibleSubstitution Γ) (σ : AdmissibleSubstitution Δ) (h : Preserves r ρ σ)
    (t : OrdinalExpression Γ) :
    expressionValue σ (ordinalExpressionRename r t) = expressionValue ρ t := by
  unfold expressionValue
  rw [AbsoluteObserver.Proof.rename_value, valuation_preserves r ρ σ h]

theorem raw_preserves {Γ Δ : List Ty} (r : Renaming Γ Δ)
    (ρ : AdmissibleSubstitution Γ) (σ : AdmissibleSubstitution Δ) (h : Preserves r ρ σ)
    (t : OriginalTerm Γ .ground) :
    rawScalar (valuation σ) (t.rename r) = rawScalar (valuation ρ) t := by
  obtain ⟨v,hv,hs⟩ := SourceCollisionCompletion.Proof.actualScalarTotal Γ t
  have hr : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (t.rename r) =
      some (SourceRenaming.renameVector r v) := by
    rw [SourceRenaming.Proof.assignmentNaturality, hv]
    rfl
  unfold rawScalar
  rw [hr, hv]
  change finiteValue (expressionValue σ (ordinalExpressionRename r (v 0))) =
    finiteValue (expressionValue ρ (v 0))
  rw [expression_preserves r ρ σ h]

theorem head_preserves {Γ Δ : List Ty} (r : Renaming Γ Δ)
    (ρ : AdmissibleSubstitution Γ) (σ : AdmissibleSubstitution Δ) (h : Preserves r ρ σ)
    (t : OriginalTerm Γ unary) :
    FunctionalDetector.Proof.value1 σ (t.rename r) = FunctionalDetector.Proof.value1 ρ t := by
  obtain ⟨v,hv,h0,h1⟩ := FunctionalDetector.Proof.values_assignment ρ t
  have hr : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (t.rename r) =
      some (SourceRenaming.renameVector r v) := by
    rw [SourceRenaming.Proof.assignmentNaturality, hv]
    rfl
  rw [FunctionalDetector.Proof.value1_of_assignment σ _ _ hr,
    FunctionalDetector.Proof.value1_of_assignment ρ _ _ hv]
  exact expression_preserves r ρ σ h _

theorem allEqual_preserves {Γ Δ : List Ty} (r : Renaming Γ Δ)
    (ρ : AdmissibleSubstitution Γ) (σ : AdmissibleSubstitution Δ) (h : Preserves r ρ σ)
    (ps : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)) :
    SourceAggregateCompletion.AllEqual (valuation σ)
      (ps.map fun p => (p.1.rename r, p.2.rename r)) ↔
    SourceAggregateCompletion.AllEqual (valuation ρ) ps := by
  constructor
  · intro hp p hmem
    have he := hp (p.1.rename r, p.2.rename r) (List.mem_map.mpr ⟨p,hmem,rfl⟩)
    change rawScalar _ (p.1.rename r) = rawScalar _ (p.2.rename r) at he
    simpa only [raw_preserves r ρ σ h] using he
  · intro hp p hmem
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hmem
    change rawScalar _ (q.1.rename r) = rawScalar _ (q.2.rename r)
    rw [raw_preserves r ρ σ h, raw_preserves r ρ σ h]
    exact hp q hq

theorem signedCNF_injective : Function.Injective SignedPair.signedCNF := by
  intro a b hab
  apply Ordinal.CNF.coeff_injective Ordinal.omega0
  ext e
  obtain ⟨m,hm⟩ := Ordinal.lt_omega0.mp (FunctionalDetector.Proof.coeff_finite a e)
  obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp (FunctionalDetector.Proof.coeff_finite b e)
  have he := congrArg (fun g : SignedPair.CantorGroup => g e) hab
  simp only [SignedPair.Proof.cnf_apply, hm, hn, SignedPair.Proof.finite_nat] at he
  have hmn : m = n := by exact_mod_cast he
  rw [hm, hn, hmn]

theorem compiled_zero_iff {n : Nat} (d : SignedPair.Expression n)
    (ρ : AdmissibleSubstitution (SignedPair.Context n)) :
    SignedPair.meaning (SignedPair.inputs ρ) d = 0 ↔
      FunctionalDetector.Proof.value1 ρ (SignedPair.compile d).pair.1 =
        FunctionalDetector.Proof.value1 ρ (SignedPair.compile d).pair.2 := by
  have hc := SignedPair.Proof.compiler_difference d ρ
  have hs : (2^(SignedPair.compile d).exponent : Int) ≠ 0 := pow_ne_zero _ (by decide)
  constructor
  · intro hd
    rw [hd, smul_zero] at hc
    apply signedCNF_injective
    exact sub_eq_zero.mp hc
  · intro hd
    have hdif : SignedPair.difference ρ (SignedPair.compile d).pair = 0 := by
      unfold SignedPair.difference
      rw [hd, sub_self]
    rw [hdif] at hc
    ext e
    have he := congrArg (fun g : SignedPair.CantorGroup => g e) hc
    change 0 = (2^(SignedPair.compile d).exponent : Int) *
      SignedPair.meaning (SignedPair.inputs ρ) d e at he
    exact (mul_eq_zero.mp he.symm).resolve_left hs

theorem headEqual_values {Γ : List Ty} (ρ : AdmissibleSubstitution Γ)
    (a b : OriginalTerm Γ unary) : HeadEqual ρ a b ↔
    FunctionalDetector.Proof.value1 ρ a = FunctionalDetector.Proof.value1 ρ b := by
  obtain ⟨av,ha,ha0,ha1⟩ := FunctionalDetector.Proof.values_assignment ρ a
  obtain ⟨bv,hb,hb0,hb1⟩ := FunctionalDetector.Proof.values_assignment ρ b
  rw [FunctionalDetector.Proof.headEqual_iff ρ a b av bv ha hb, ha1, hb1]

theorem pad_head_value {Γ : List Ty} (ρ : AdmissibleSubstitution Γ)
    (a : OriginalTerm Γ unary) (q : OriginalTerm Γ .ground) :
    FunctionalDetector.Proof.value1 ρ (pad a q) =
      FunctionalDetector.Proof.paddedHead (FunctionalDetector.Proof.value1 ρ a) := by
  obtain ⟨av,ha,ha0,ha1⟩ := FunctionalDetector.Proof.values_assignment ρ a
  obtain ⟨qv,hq,hqs⟩ := SourceCollisionCompletion.Proof.actualScalarTotal Γ q
  rw [FunctionalDetector.Proof.value1_of_assignment ρ _ _
    (FunctionalDetector.Proof.pad_assignment a q av qv ha hq)]
  change denote (valuation ρ) (FunctionalDetector.Proof.padVector av qv 1) = _
  rw [FunctionalDetector.Proof.pad_head]
  change FunctionalDetector.Proof.paddedHead (expressionValue ρ (av 1)) = _
  rw [ha1]

/-- Reverse alignment for an arbitrary admissible assignment of the fresh
ground wires, rather than only the specially constructed extension. -/
theorem aligned_reverse {Γ : List Ty} (a b : OriginalTerm Γ unary)
    (σ : AdmissibleSubstitution (.ground::.ground::Γ))
    (h : VectorEqual σ (alignedLeft a) (alignedRight b)) :
    FunctionalDetector.Proof.value1 (pullback (shiftTwo Γ) σ) a =
      FunctionalDetector.Proof.value1 (pullback (shiftTwo Γ) σ) b := by
  have he := (FunctionalDetector.Proof.vector_equal_values σ _ _).mp h
  have hh := he.2
  change FunctionalDetector.Proof.value1 σ (pad (a.rename (shiftTwo Γ)) (.var .here)) =
    FunctionalDetector.Proof.value1 σ (pad (b.rename (shiftTwo Γ)) (.var (.there .here))) at hh
  rw [pad_head_value, pad_head_value] at hh
  have hv := FunctionalDetector.Proof.paddedHead_injective hh
  simpa only [head_preserves (shiftTwo Γ) (pullback (shiftTwo Γ) σ) σ
    (fun _ _ _ => rfl)] using hv

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SystemProof
