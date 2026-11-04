module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSystemTargets
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSolvabilityProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SystemRenamingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSystem.Proof
open OriginalDomain FunctionalDetector SourceCollisionCompletion SystemProof

private theorem compiled_zero_iff {n : Nat} (d : SignedPair.Expression n)
    (ρ : AdmissibleSubstitution (SignedPair.Context n)) :
    SignedPair.meaning (SeededCompiler.seededInputs ρ) (SeededCompiler.subtractSeed d)=0 ↔
      FunctionalDetector.Proof.value1 ρ (SeededCompiler.compile (SeededCompiler.subtractSeed d)).pair.1=
        FunctionalDetector.Proof.value1 ρ (SeededCompiler.compile (SeededCompiler.subtractSeed d)).pair.2 := by
  have hc := SeededCompiler.Proof.compiler_difference (SeededCompiler.subtractSeed d) ρ
  have hs : (2^(SeededCompiler.compile (SeededCompiler.subtractSeed d)).exponent : Int)≠0 :=
    pow_ne_zero _ (by decide)
  constructor
  · intro hd
    rw [hd,smul_zero] at hc
    exact signedCNF_injective (sub_eq_zero.mp hc)
  · intro hd
    have hdif : SignedPair.difference ρ (SeededCompiler.compile (SeededCompiler.subtractSeed d)).pair=0 := by
      unfold SignedPair.difference
      rw [hd,sub_self]
    rw [hdif] at hc
    ext e
    have he := congrArg (fun g : SignedPair.CantorGroup => g e) hc
    change 0=(2^(SeededCompiler.compile (SeededCompiler.subtractSeed d)).exponent : Int)*
      SignedPair.meaning (SeededCompiler.seededInputs ρ) (SeededCompiler.subtractSeed d) e at he
    exact (mul_eq_zero.mp he.symm).resolve_left hs

theorem valuationPreservingSystem : Targets.ExactValuationPreservation := by
  intro n s
  induction s with
  | nil =>
      intro ρ
      constructor
      · intro _
        exact ⟨ρ, (fun _ _ _ => rfl), (by
          intro p hp
          exact False.elim (List.not_mem_nil hp))⟩
      · intro _ d hd
        exact False.elim (List.not_mem_nil hd)
  | cons d ds ih =>
      intro ρ
      let t := compile ds
      let a := (SeededCompiler.compile (SeededCompiler.subtractSeed d)).pair.1.rename t.original
      let b := (SeededCompiler.compile (SeededCompiler.subtractSeed d)).pair.2.rename t.original
      change Solves (d::ds) ρ ↔
        ∃ σ : AdmissibleSubstitution (.ground::.ground::t.context),
          Preserves (fun {_} x => shiftTwo t.context (t.original x)) ρ σ ∧
          SourceAggregateCompletion.AllEqual (valuation σ)
            ((left (alignedLeft a) (alignedRight b), right (alignedLeft a) (alignedRight b))::
              t.detectors.map (fun p =>
                (p.1.rename (shiftTwo t.context), p.2.rename (shiftTwo t.context))))
      constructor
      · intro hs
        have hd := hs d (List.mem_cons_self)
        have hds : Solves ds ρ := fun e he => hs e (List.mem_cons_of_mem _ he)
        obtain ⟨θ,hθ,hall⟩ := (ih ρ).mp hds
        have hh : HeadEqual θ a b := by
          apply (headEqual_values θ a b).mpr
          dsimp only [a,b]
          rw [head_preserves t.original ρ θ hθ, head_preserves t.original ρ θ hθ]
          exact (compiled_zero_iff d ρ).mp hd
        obtain ⟨z,w,hvec⟩ := (FunctionalDetector.Proof.alignment t.context a b θ).mp hh
        let σ := extend θ z w
        refine ⟨σ, ?_, ?_⟩
        · intro τ x j
          change θ.vector (t.original x) j = ρ.vector x j
          exact hθ τ x j
        · apply (SourceAggregateCompletion.Proof.all_equal_cons _ _ _ _).mpr
          constructor
          · exact (FunctionalDetector.Proof.detector σ (alignedLeft a) (alignedRight b)).2.1.mpr hvec
          · exact (allEqual_preserves (shiftTwo t.context) θ σ (fun _ _ _ => rfl) _).mpr hall
      · rintro ⟨σ,hσ,hall⟩
        let θ := pullback (shiftTwo t.context) σ
        have hθ : Preserves t.original ρ θ := by
          intro τ x j
          exact hσ τ x j
        have hpairs := (SourceAggregateCompletion.Proof.all_equal_cons _ _ _ _).mp hall
        have hvec := (FunctionalDetector.Proof.detector σ (alignedLeft a) (alignedRight b)).2.1.mp hpairs.1
        have hh := aligned_reverse a b σ hvec
        have hd : SignedPair.meaning (SeededCompiler.seededInputs ρ) (SeededCompiler.subtractSeed d) = 0 := by
          apply (compiled_zero_iff d ρ).mpr
          dsimp only [a,b] at hh
          rw [head_preserves t.original ρ θ hθ, head_preserves t.original ρ θ hθ] at hh
          exact hh
        have htail := (allEqual_preserves (shiftTwo t.context) θ σ (fun _ _ _ => rfl) _).mp hpairs.2
        have hds := (ih ρ).mpr ⟨θ,hθ,htail⟩
        intro e he
        rcases List.mem_cons.mp he with he | he
        · subst e
          exact hd
        · exact hds e he

theorem valuationEquality (n : Nat) (s : System n) :
    (∃ ρ : AdmissibleSubstitution (SignedPair.Context n),Solves s ρ) ↔
      ∃ ρ : AdmissibleSubstitution (compile s).context,
        rawScalar (valuation ρ) (strictPair s).1=rawScalar (valuation ρ) (strictPair s).2 := by
  constructor
  · rintro ⟨ρ,hρ⟩
    obtain ⟨σ,hσ,he⟩ := (valuationPreservingSystem n s ρ).mp hρ
    refine ⟨σ, ?_⟩
    exact (SourceAggregateCompletion.Proof.admissible_aggregate _ _ σ).2.1.mpr he
  · rintro ⟨σ,he⟩
    let ρ := pullback (compile s).original σ
    refine ⟨ρ, (valuationPreservingSystem n s ρ).mpr ?_⟩
    exact ⟨σ, (fun _ _ _ => rfl),
      (SourceAggregateCompletion.Proof.admissible_aggregate _ _ σ).2.1.mp he⟩

theorem exactSystemEquality : Targets.ExactSystemEquality := by
  intro n s
  exact (SeededCompiler.Proof.exactSeededSatisfiability n s).trans (valuationEquality n s)

private theorem strict_complement (n : Nat) (s : System n) :
    universalStrict s ↔ ¬PolynomialSatisfiable s := by
  constructor
  · intro hu hs
    obtain ⟨ρ,he⟩ := (exactSystemEquality n s).mp hs
    have hh := hu ρ
    omega
  · intro hn ρ
    have ha := SourceAggregateCompletion.Proof.admissible_aggregate _ (compile s).detectors ρ
    have hne : rawScalar (valuation ρ) (strictPair s).1≠rawScalar (valuation ρ) (strictPair s).2 := by
      intro he
      exact hn ((exactSystemEquality n s).mpr ⟨ρ,he⟩)
    have hle := ha.1
    change rawScalar _ (strictPair s).2≤rawScalar _ (strictPair s).1 at hle
    omega

private theorem weak_iff_strict {n : Nat} (s : System n)
    (ρ : AdmissibleSubstitution (compile s).context) :
    rawScalar (valuation ρ) (weakPair s).1≤rawScalar (valuation ρ) (weakPair s).2 ↔
      rawScalar (valuation ρ) (strictPair s).2<rawScalar (valuation ρ) (strictPair s).1 := by
  unfold weakPair ParametricLiteralWeakWrapper.constantApply ParametricLiteralWeakWrapper.identityApply
  rw [GroundEquivalence.Proof.constant_raw,GroundEquivalence.Proof.identity_raw,GroundEquivalence.Proof.g_le_iff]
  have ha := SourceAggregateCompletion.Proof.admissible_aggregate _ (compile s).detectors ρ
  constructor
  · intro h
    omega
  · intro h
    have hn : ¬SourceAggregateCompletion.AllEqual (valuation ρ) (compile s).detectors := by
      intro he
      have hh := ha.2.1.mpr he
      change rawScalar _ (strictPair s).1=rawScalar _ (strictPair s).2 at hh
      omega
    have hgap := ha.2.2 hn
    change 2≤rawScalar _ (strictPair s).1-rawScalar _ (strictPair s).2 at hgap
    omega

theorem exactSingleQuerySemantics : Targets.ExactSingleQuerySemantics := by
  intro n s
  exact ⟨strict_complement n s,
    (forall_congr' (fun ρ => weak_iff_strict s ρ)).trans (strict_complement n s)⟩

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSystem.Proof
