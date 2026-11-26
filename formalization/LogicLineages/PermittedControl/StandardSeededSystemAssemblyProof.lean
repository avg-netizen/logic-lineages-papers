module
public import LogicLineages.PermittedControl.StandardSystemAssemblyProof
public import LogicLineages.PermittedControl.StandardSeededSystemTargets
public import LogicLineages.PermittedControl.StandardSeededCompilerProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardSeededSystem.Proof
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector
open Source.AdmissibleSum
open StandardFunctionalDetector.Proof
open Source.FunctionalDetector (unary shiftTwo alignedLeft alignedRight left right)
open Source.FunctionalHardnessCompletion
open SelectedSystemReduction
open SelectedSeededSystem (Solves)
open StandardSystemMask.Proof (all_equal_cons headEqual_values head_preserves allEqual_preserves aligned_reverse)
open SelectedHardness (value1)

private theorem signedCNF_injective : Function.Injective SignedPair.signedCNF := by
  intro a b hab
  apply Ordinal.CNF.coeff_injective Ordinal.omega0
  ext e
  obtain ⟨m,hm⟩ := Ordinal.lt_omega0.mp (FunctionalDetector.Proof.coeff_finite a e)
  obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp (FunctionalDetector.Proof.coeff_finite b e)
  have he := congrArg (fun g : SignedPair.CantorGroup => g e) hab
  simp only [SignedPair.Proof.cnf_apply,hm,hn,SignedPair.Proof.finite_nat] at he
  have hmn : m=n := by exact_mod_cast he
  rw [hm,hn,hmn]

/-- Zero meaning of a seeded expression is equality of the two compiled source
heads at Phi, from the rebuilt Phi seeded compiler identity. -/
theorem seeded_compiled_zero_iff
    (policy : Policy) {n : Nat} (d : SignedPair.Expression (n+1))
    (ρ : AdmissibleSubstitution Phi (SignedPair.Context n)) :
    SignedPair.meaning (SelectedSeededCompiler.seededInputs Phi ρ) d=0 ↔
    value1 Phi policy ρ (SeededCompiler.compile d).pair.1=value1 Phi policy ρ (SeededCompiler.compile d).pair.2 := by
  have hcomp := StandardSeededCompiler.Proof.compiler_difference policy d ρ
  have hs : (2^(SeededCompiler.compile d).exponent : Int)≠0 := pow_ne_zero _ (by decide)
  constructor
  · intro hd
    rw [hd,smul_zero] at hcomp
    apply signedCNF_injective
    exact sub_eq_zero.mp hcomp
  · intro hd
    have hz : SelectedPairCompiler.difference Phi policy ρ (SeededCompiler.compile d).pair=0 := by
      unfold SelectedPairCompiler.difference
      rw [hd,sub_self]
    rw [hz] at hcomp
    ext e
    have he := congrArg (fun g : SignedPair.CantorGroup => g e) hcomp
    change 0=(2^(SeededCompiler.compile d).exponent : Int)*
      SignedPair.meaning (SelectedSeededCompiler.seededInputs Phi ρ) d e at he
    exact (mul_eq_zero.mp he.symm).resolve_left hs

theorem valuationPreservation : StandardSeededSystem.ValuationPreservation := by
  intro policy n s
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
      let t := SeededSystem.compile ds
      let a := (SeededCompiler.compile (SeededCompiler.subtractSeed d)).pair.1.rename t.original
      let b := (SeededCompiler.compile (SeededCompiler.subtractSeed d)).pair.2.rename t.original
      change Solves Phi (d::ds) ρ ↔
        ∃ σ : AdmissibleSubstitution Phi (.ground::.ground::t.context),
          Preserves Phi (fun {_} x => shiftTwo t.context (t.original x)) ρ σ ∧
          SelectedAggregation.AllEqual Phi policy σ
            ((left (alignedLeft a) (alignedRight b), right (alignedLeft a) (alignedRight b))::
              t.detectors.map (fun p =>
                (p.1.rename (shiftTwo t.context), p.2.rename (shiftTwo t.context))))
      constructor
      · intro hs
        have hd := hs d (List.mem_cons_self)
        have hds : Solves Phi ds ρ := fun e he => hs e (List.mem_cons_of_mem _ he)
        obtain ⟨θ,hθ,hall⟩ := (ih ρ).mp hds
        have hh : HeadEqual Phi policy θ a b := by
          apply (headEqual_values policy θ a b).mpr
          dsimp only [a,b]
          rw [head_preserves Phi t.original ρ θ hθ policy, head_preserves Phi t.original ρ θ hθ policy]
          exact (seeded_compiled_zero_iff policy (SeededCompiler.subtractSeed d) ρ).mp hd
        obtain ⟨z,w,hvec⟩ := (alignment policy t.context a b θ).mp hh
        let σ := extend Phi θ z w
        refine ⟨σ, ?_, ?_⟩
        · intro τ x j
          change θ.vector (t.original x) j = ρ.vector x j
          exact hθ τ x j
        · apply (all_equal_cons Phi policy _ _ _).mpr
          constructor
          · exact (detector policy σ (alignedLeft a) (alignedRight b)).2.2.1.mpr hvec
          · exact (allEqual_preserves Phi (shiftTwo t.context) θ σ (fun _ _ _ => rfl) policy _).mpr hall
      · rintro ⟨σ,hσ,hall⟩
        let θ := pullback Phi (shiftTwo t.context) σ
        have hθ : Preserves Phi t.original ρ θ := by
          intro τ x j
          exact hσ τ x j
        have hpairs := (all_equal_cons Phi policy _ _ _).mp hall
        have hvec := (detector policy σ (alignedLeft a) (alignedRight b)).2.2.1.mp hpairs.1
        have hh := aligned_reverse policy a b σ hvec
        have hd : SignedPair.meaning (SelectedSeededCompiler.seededInputs Phi ρ) (SeededCompiler.subtractSeed d) = 0 := by
          apply (seeded_compiled_zero_iff policy (SeededCompiler.subtractSeed d) ρ).mpr
          dsimp only [a,b] at hh
          rw [head_preserves Phi t.original ρ θ hθ policy, head_preserves Phi t.original ρ θ hθ policy] at hh
          exact hh
        have htail := (allEqual_preserves Phi (shiftTwo t.context) θ σ (fun _ _ _ => rfl) policy _).mp hpairs.2
        have hds := (ih ρ).mpr ⟨θ,hθ,htail⟩
        intro e he
        rcases List.mem_cons.mp he with he | he
        · subst e
          exact hd
        · exact hds e he
end LogicLineages.PermittedControl.StandardSeededSystem.Proof
