module
public import LogicLineages.PermittedControl.SelectedSystemAlignmentProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSystemReduction.Proof
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector
open Source.AdmissibleSum
open SelectedFunctionalDetector.Proof
open Source.FunctionalDetector (unary shiftTwo alignedLeft alignedRight left right)
open Source.FunctionalHardnessCompletion (System compileSystem strictSystemPair weakSystemPair)

 theorem all_equal_cons {Γ} (ctrl : Nat → Nat) (policy : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) (e : OriginalTerm Γ .ground × OriginalTerm Γ .ground)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)) :
    SelectedAggregation.AllEqual ctrl policy ρ (e::es) ↔
    groundValue ctrl policy ρ e.1=groundValue ctrl policy ρ e.2 ∧ SelectedAggregation.AllEqual ctrl policy ρ es := by
  simp [SelectedAggregation.AllEqual]

theorem valuationPreservingSystem : SelectedSystemReductionTargets.ValuationPreservingSystem := by
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
      let t := compileSystem ds
      let a := (SignedPair.compile d).pair.1.rename t.original
      let b := (SignedPair.compile d).pair.2.rename t.original
      change OrdinalSolves ctrl (d::ds) ρ ↔
        ∃ σ : AdmissibleSubstitution ctrl (.ground::.ground::t.context),
          Preserves ctrl (fun {_} x => shiftTwo t.context (t.original x)) ρ σ ∧
          SelectedAggregation.AllEqual ctrl policy σ
            ((left (alignedLeft a) (alignedRight b), right (alignedLeft a) (alignedRight b))::
              t.detectors.map (fun p =>
                (p.1.rename (shiftTwo t.context), p.2.rename (shiftTwo t.context))))
      constructor
      · intro hs
        have hd := hs d (List.mem_cons_self)
        have hds : OrdinalSolves ctrl ds ρ := fun e he => hs e (List.mem_cons_of_mem _ he)
        obtain ⟨θ,hθ,hall⟩ := (ih ρ).mp hds
        have hh : HeadEqual ctrl policy θ a b := by
          apply (headEqual_values ctrl K hc policy θ a b).mpr
          dsimp only [a,b]
          rw [head_preserves ctrl t.original ρ θ hθ policy, head_preserves ctrl t.original ρ θ hθ policy]
          exact (compiled_zero_iff ctrl K hc policy d ρ).mp hd
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
        have hd : SignedPair.meaning (SelectedPairCompiler.inputs ctrl ρ) d = 0 := by
          apply (compiled_zero_iff ctrl K hc policy d ρ).mpr
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

end LogicLineages.PermittedControl.SelectedSystemReduction.Proof
