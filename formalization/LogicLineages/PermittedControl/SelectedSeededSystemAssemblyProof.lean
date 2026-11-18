module
public import LogicLineages.PermittedControl.SelectedSystemAssemblyProof
public import LogicLineages.PermittedControl.SelectedSeededSystemTargets
public import LogicLineages.PermittedControl.SelectedSeededSolvabilityProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSeededSystem.Proof
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector
open Source.AdmissibleSum
open SelectedFunctionalDetector.Proof
open Source.FunctionalDetector (unary shiftTwo alignedLeft alignedRight left right)
open Source.FunctionalHardnessCompletion
open SelectedSystemReduction SelectedSystemReduction.Proof
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

 theorem compiled_zero_iff (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (policy : Policy) {n : Nat} (d : SignedPair.Expression (n+1))
    (ρ : AdmissibleSubstitution ctrl (SignedPair.Context n)) :
    SignedPair.meaning (SelectedSeededCompiler.seededInputs ctrl ρ) d=0 ↔
    value1 ctrl policy ρ (SeededCompiler.compile d).pair.1=value1 ctrl policy ρ (SeededCompiler.compile d).pair.2 := by
  have hcomp := SelectedSeededCompiler.Proof.compiler_difference ctrl K hc policy d ρ
  have hs : (2^(SeededCompiler.compile d).exponent : Int)≠0 := pow_ne_zero _ (by decide)
  constructor
  · intro hd
    rw [hd,smul_zero] at hcomp
    apply signedCNF_injective
    exact sub_eq_zero.mp hcomp
  · intro hd
    have hz : SelectedPairCompiler.difference ctrl policy ρ (SeededCompiler.compile d).pair=0 := by
      unfold SelectedPairCompiler.difference
      rw [hd,sub_self]
    rw [hz] at hcomp
    ext e
    have he := congrArg (fun g : SignedPair.CantorGroup => g e) hcomp
    change 0=(2^(SeededCompiler.compile d).exponent : Int)*
      SignedPair.meaning (SelectedSeededCompiler.seededInputs ctrl ρ) d e at he
    exact (mul_eq_zero.mp he.symm).resolve_left hs



theorem valuationPreservingSystem : SelectedSeededSystemTargets.ValuationPreservation := by
  intro ctrl K hc policy n s
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
      change Solves ctrl (d::ds) ρ ↔
        ∃ σ : AdmissibleSubstitution ctrl (.ground::.ground::t.context),
          Preserves ctrl (fun {_} x => shiftTwo t.context (t.original x)) ρ σ ∧
          SelectedAggregation.AllEqual ctrl policy σ
            ((left (alignedLeft a) (alignedRight b), right (alignedLeft a) (alignedRight b))::
              t.detectors.map (fun p =>
                (p.1.rename (shiftTwo t.context), p.2.rename (shiftTwo t.context))))
      constructor
      · intro hs
        have hd := hs d (List.mem_cons_self)
        have hds : Solves ctrl ds ρ := fun e he => hs e (List.mem_cons_of_mem _ he)
        obtain ⟨θ,hθ,hall⟩ := (ih ρ).mp hds
        have hh : HeadEqual ctrl policy θ a b := by
          apply (headEqual_values ctrl K hc policy θ a b).mpr
          dsimp only [a,b]
          rw [head_preserves ctrl t.original ρ θ hθ policy, head_preserves ctrl t.original ρ θ hθ policy]
          exact (compiled_zero_iff ctrl K hc policy (SeededCompiler.subtractSeed d) ρ).mp hd
        obtain ⟨z,w,hvec⟩ := (alignment ctrl K hc policy t.context a b θ).mp hh
        let σ := extend ctrl θ z w
        refine ⟨σ, ?_, ?_⟩
        · intro τ x j
          change θ.vector (t.original x) j = ρ.vector x j
          exact hθ τ x j
        · apply (all_equal_cons ctrl policy _ _ _).mpr
          constructor
          · exact (detector ctrl K hc policy σ (alignedLeft a) (alignedRight b)).2.2.1.mpr hvec
          · exact (allEqual_preserves ctrl (shiftTwo t.context) θ σ (fun _ _ _ => rfl) policy _).mpr hall
      · rintro ⟨σ,hσ,hall⟩
        let θ := pullback ctrl (shiftTwo t.context) σ
        have hθ : Preserves ctrl t.original ρ θ := by
          intro τ x j
          exact hσ τ x j
        have hpairs := (all_equal_cons ctrl policy _ _ _).mp hall
        have hvec := (detector ctrl K hc policy σ (alignedLeft a) (alignedRight b)).2.2.1.mp hpairs.1
        have hh := aligned_reverse ctrl K hc policy a b σ hvec
        have hd : SignedPair.meaning (SelectedSeededCompiler.seededInputs ctrl ρ) (SeededCompiler.subtractSeed d) = 0 := by
          apply (compiled_zero_iff ctrl K hc policy (SeededCompiler.subtractSeed d) ρ).mpr
          dsimp only [a,b] at hh
          rw [head_preserves ctrl t.original ρ θ hθ policy, head_preserves ctrl t.original ρ θ hθ policy] at hh
          exact hh
        have htail := (allEqual_preserves ctrl (shiftTwo t.context) θ σ (fun _ _ _ => rfl) policy _).mp hpairs.2
        have hds := (ih ρ).mpr ⟨θ,hθ,htail⟩
        intro e he
        rcases List.mem_cons.mp he with he | he
        · subst e
          exact hd
        · exact hds e he

end LogicLineages.PermittedControl.SelectedSeededSystem.Proof
