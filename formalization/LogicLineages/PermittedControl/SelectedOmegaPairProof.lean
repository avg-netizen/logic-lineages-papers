module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.OmegaScaleAlgebraProof
public import LogicLineages.PermittedControl.SelectedOmegaHigherProof
public import LogicLineages.PermittedControl.SelectedPairCompilerAlgebraProof
public import LogicLineages.PermittedControl.SelectedDetectorPayloadProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedOmegaSeed.Proof
open OrdinalComparison Source SelectedSourceDomain AdmissibleAssignment
open FunctionalDetector (unary)
open FunctionalDetector.Proof
open Source.FunctionalHardnessCompletion.OmegaSeed (source higherUnary)
open Source.FunctionalHardnessCompletion.OmegaSeed.Proof (seedShift principal_product_cnf principal_cnf)
open SelectedHardness (value1)
open SignedPair SignedPair.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem application_head_expression (policy : AdmissibleSum.Policy) {Γ} (hv : OrdinalVector Γ 2)
    (av : OrdinalVector Γ 1) :
    application (σ:=unary) (τ:=unary) policy hv av 1 =
      .emul (hv 2) (.add (hv 1) (av 1)) := by
  simp [application,box,ordinalBoxPositive,ordinalVectorAt,unary,Ty.level]
  exact ⟨rfl,rfl,rfl⟩

private theorem apply_source_head (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (policy : AdmissibleSum.Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ)
    (hv : OrdinalVector Γ 2)
    (hh : assignment policy source=some hv)
    (a : OriginalTerm Γ unary) :
    value1 ctrl policy ρ (.app source a) = ordinalNaturalProduct (omega ctrl)
      (ordinalNaturalSum (expressionValue ctrl ρ (hv 1)) (value1 ctrl policy ρ a)) := by
  obtain ⟨av,ha,_,ha1⟩ := SelectedFunctionalDetector.Proof.values_assignment ctrl K hc policy ρ a
  have h2 : expressionValue ctrl ρ (hv 2)=exponent ctrl := by
    have h := source_second ctrl policy ρ
    unfold secondValue at h
    rw [hh] at h
    change expressionValue ctrl ρ (hv 2)=exponent ctrl at h
    exact h
  calc
    value1 ctrl policy ρ (.app source a) = expressionValue ctrl ρ
        (application (σ:=unary) (τ:=unary) policy hv av 1) :=
      SelectedHardnessCoordinatesProof.value1_of_assignment ctrl policy ρ _ _ (SelectedHardnessCombinatorSyntaxProof.app_assignment policy _ _ _ _ hh ha)
    _ = expressionValue ctrl ρ (.emul (hv 2) (.add (hv 1) (av 1))) :=
      congrArg (expressionValue ctrl ρ) (application_head_expression policy hv av)
    _ = ordinalNaturalProduct (omega ctrl)
        (ordinalNaturalSum (expressionValue ctrl ρ (hv 1)) (value1 ctrl policy ρ a)) := by
      change ordinalNaturalProduct ((2 : Ordinal)^expressionValue ctrl ρ (hv 2))
        (ordinalNaturalSum (expressionValue ctrl ρ (hv 1)) (expressionValue ctrl ρ (av 1)))=_
      rw [h2, exponent_calibration, ←Source.FunctionalHardnessCompletion.OmegaSeed.Proof.omega_power, ha1, omega_calibration]

private theorem apply_source_bound {Γ} (a : OriginalTerm Γ unary)
    (ha : SourceClasses.InternalLevelBound 2 a) :
    SourceClasses.InternalLevelBound 3 (.app source a) := by
  intro σ hσ
  change σ ∈ unary.subtypes.toFinset ∪
    (SourceTypeSupport.typeSupport source ∪ SourceTypeSupport.typeSupport a) at hσ
  rcases Finset.mem_union.mp hσ with hσ | hσ
  · have h : σ=unary ∨ σ=.ground := by
      simpa [unary,Ty.subtypes] using List.mem_toFinset.mp hσ
    rcases h with rfl | rfl <;> decide
  · rcases Finset.mem_union.mp hσ with hσ | hσ
    · exact Source.FunctionalHardnessCompletion.OmegaSeed.Proof.source_bound Γ σ hσ
    · exact (ha σ hσ).trans (by decide)

theorem actualScaledPair : SelectedOmegaSeedTargets.ActualScaledPair := by
  intro ctrl K hc Γ policy ρ
  refine ⟨apply_source_bound _ unit_bound.1,apply_source_bound _ unit_bound.2,?_,?_⟩
  · obtain ⟨av,ha,_,_⟩ := SelectedFunctionalDetector.Proof.values_assignment ctrl K hc policy ρ (.app source unitPair.1)
    obtain ⟨bv,hb,_,_⟩ := SelectedFunctionalDetector.Proof.values_assignment ctrl K hc policy ρ (.app source unitPair.2)
    refine ⟨av,bv,ha,hb,?_,?_⟩
    · rw [←SelectedHardnessCoordinatesProof.value1_of_assignment ctrl policy ρ _ _ ha]
      exact (SelectedFunctionalDetector.Proof.values_facts ctrl K hc policy ρ _).2.1
    · rw [←SelectedHardnessCoordinatesProof.value1_of_assignment ctrl policy ρ _ _ hb]
      exact (SelectedFunctionalDetector.Proof.values_facts ctrl K hc policy ρ _).2.1
  let hv := higherVector policy (higherVector policy (identityVector policy Γ))
  have hh : assignment policy source=some hv := source_assignment policy Γ
  obtain ⟨e,he0⟩ := Source.FunctionalHardnessCompletion.OmegaSeed.Proof.omega_principal
  have he : omega ctrl=Ordinal.omega0^e.1.repr := (omega_calibration ctrl).trans he0
  have hscale (a : OriginalTerm Γ unary) :
      signedCNF (value1 ctrl policy ρ (.app source a)) = seedShift e.1.repr
        (signedCNF (expressionValue ctrl ρ (hv 1))+signedCNF (value1 ctrl policy ρ a)) := by
    have hb := sum_below_epsilon _ _
      (SelectedValueClosureProof.ambient_below ctrl ρ (hv 1)) (SelectedFunctionalDetector.Proof.values_facts ctrl K hc policy ρ a).2.2.1
    have hhead := apply_source_head ctrl K hc policy ρ hv hh a
    have hm := congrArg (fun o => ordinalNaturalProduct o
      (ordinalNaturalSum (expressionValue ctrl ρ (hv 1)) (value1 ctrl policy ρ a))) he
    calc
      signedCNF (value1 ctrl policy ρ (.app source a)) = signedCNF
          (ordinalNaturalProduct (Ordinal.omega0^e.1.repr)
            (ordinalNaturalSum (expressionValue ctrl ρ (hv 1)) (value1 ctrl policy ρ a))) :=
        congrArg signedCNF (hhead.trans hm)
      _ = seedShift e.1.repr (signedCNF
          (ordinalNaturalSum (expressionValue ctrl ρ (hv 1)) (value1 ctrl policy ρ a))) :=
        principal_product_cnf e _ hb
      _ = seedShift e.1.repr
          (signedCNF (expressionValue ctrl ρ (hv 1))+signedCNF (value1 ctrl policy ρ a)) :=
        congrArg (seedShift e.1.repr) (cnf_sum _ _)
  have hz : ordinalNaturalSum e.1.repr 0=e.1.repr := by
    simpa only [Nat.cast_zero,add_zero] using actualNaturalSumFiniteRight e.1.repr 0
  have hone : seedShift e.1.repr (signedCNF 1)=signedCNF (omega ctrl) := by
    calc
      seedShift e.1.repr (signedCNF 1) = Finsupp.single e.1.repr 1 := by
        change Finsupp.mapDomain (ordinalNaturalSum e.1.repr) (signedCNF 1)=_
        have hc1 : signedCNF (1 : Ordinal)=Finsupp.single 0 (1 : Int) := by
          simpa only [Nat.cast_one] using cnf_nat 1
        calc
          Finsupp.mapDomain (ordinalNaturalSum e.1.repr) (signedCNF 1) =
              Finsupp.mapDomain (ordinalNaturalSum e.1.repr) (Finsupp.single 0 (1 : Int)) :=
            congrArg (Finsupp.mapDomain (ordinalNaturalSum e.1.repr)) hc1
          _ = Finsupp.single (ordinalNaturalSum e.1.repr 0) 1 := Finsupp.mapDomain_single
          _ = Finsupp.single e.1.repr 1 := congrArg (fun a => Finsupp.single a (1 : Int)) hz
      _ = signedCNF (Ordinal.omega0^e.1.repr) := (principal_cnf _).symm
      _ = signedCNF (omega ctrl) := congrArg signedCNF he.symm
  change signedCNF (value1 ctrl policy ρ (.app source unitPair.1))-
    signedCNF (value1 ctrl policy ρ (.app source unitPair.2))=(2^12 : Int) • signedCNF (omega ctrl)
  calc
    signedCNF (value1 ctrl policy ρ (.app source unitPair.1))-
        signedCNF (value1 ctrl policy ρ (.app source unitPair.2)) =
        seedShift e.1.repr (signedCNF (expressionValue ctrl ρ (hv 1))+signedCNF (value1 ctrl policy ρ unitPair.1))-
        seedShift e.1.repr (signedCNF (expressionValue ctrl ρ (hv 1))+signedCNF (value1 ctrl policy ρ unitPair.2)) :=
      congrArg₂ (fun a b : CantorGroup => a-b) (hscale unitPair.1) (hscale unitPair.2)
    _ = seedShift e.1.repr
        ((signedCNF (expressionValue ctrl ρ (hv 1))+signedCNF (value1 ctrl policy ρ unitPair.1))-
         (signedCNF (expressionValue ctrl ρ (hv 1))+signedCNF (value1 ctrl policy ρ unitPair.2))) :=
      (map_sub (seedShift e.1.repr) _ _).symm
    _ = seedShift e.1.repr (SelectedPairCompiler.difference ctrl policy ρ unitPair) := by
      apply congrArg (seedShift e.1.repr)
      unfold SelectedPairCompiler.difference
      abel
    _ = seedShift e.1.repr ((2^12 : Int) • signedCNF 1) :=
      congrArg (seedShift e.1.repr) (SelectedPairCompiler.Proof.unit_difference ctrl K hc policy ρ)
    _ = (2^12 : Int) • seedShift e.1.repr (signedCNF 1) :=
      (seedShift e.1.repr).map_zsmul (2^12 : Int) (signedCNF 1)
    _ = (2^12 : Int) • signedCNF (omega ctrl) := congrArg (fun a => (2^12 : Int) • a) hone

end LogicLineages.PermittedControl.SelectedOmegaSeed.Proof
