module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.OmegaScaleAlgebraProof
public import LogicLineages.OrdinalComparison.WWOriginalValueClosureProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.OmegaSeed.Proof
open OriginalDomain AdmissibleAssignment FunctionalDetector FunctionalDetector.Proof
open SignedPair SignedPair.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem application_head_expression {Γ} (hv : OrdinalVector Γ 2)
    (av : OrdinalVector Γ 1) :
    application (σ:=unary) (τ:=unary) OrdinalSyntax.defaultPolicy hv av 1 =
      .emul (hv 2) (.add (hv 1) (av 1)) := by
  simp [application,box,ordinalBoxPositive,ordinalVectorAt,unary,Ty.level]
  exact ⟨rfl,rfl,rfl⟩

private theorem apply_source_head {Γ} (ρ : AdmissibleSubstitution Γ)
    (hv : OrdinalVector Γ 2)
    (hh : assignment OrdinalSyntax.defaultPolicy source=some hv)
    (a : OriginalTerm Γ unary) :
    value1 ρ (.app source a) = ordinalNaturalProduct omega
      (ordinalNaturalSum (expressionValue ρ (hv 1)) (value1 ρ a)) := by
  obtain ⟨av,ha,_,ha1⟩ := values_assignment ρ a
  have h2 : expressionValue ρ (hv 2)=exponent := by
    have h := source_second ρ
    unfold secondValue at h
    rw [hh] at h
    change expressionValue ρ (hv 2)=exponent at h
    exact h
  calc
    value1 ρ (.app source a) = expressionValue ρ
        (application (σ:=unary) (τ:=unary) OrdinalSyntax.defaultPolicy hv av 1) :=
      value1_of_assignment ρ _ _ (AbsoluteObserver.Proof.app_assignment _ _ _ _ hh ha)
    _ = expressionValue ρ (.emul (hv 2) (.add (hv 1) (av 1))) :=
      congrArg (expressionValue ρ) (application_head_expression hv av)
    _ = ordinalNaturalProduct omega
        (ordinalNaturalSum (expressionValue ρ (hv 1)) (value1 ρ a)) := by
      change ordinalNaturalProduct ((2 : Ordinal)^expressionValue ρ (hv 2))
        (ordinalNaturalSum (expressionValue ρ (hv 1)) (expressionValue ρ (av 1)))=_
      rw [h2,←omega_power,ha1]

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
    · exact source_bound Γ σ hσ
    · exact (ha σ hσ).trans (by decide)

theorem actualScaledPair : Targets.ActualScaledPair := by
  intro Γ ρ
  refine ⟨apply_source_bound _ unit_bound.1,apply_source_bound _ unit_bound.2,?_⟩
  obtain ⟨hv,hh,_⟩ := actualAdmissibleAssignmentGenerated Γ higherUnary
    OrdinalSyntax.defaultPolicy source
  obtain ⟨e,he⟩ := omega_principal
  have hscale (a : OriginalTerm Γ unary) :
      signedCNF (value1 ρ (.app source a)) = seedShift e.1.repr
        (signedCNF (expressionValue ρ (hv 1))+signedCNF (value1 ρ a)) := by
    have hb := sum_below_epsilon _ _
      (originalExpressionValueBelowEpsilonZero Γ ρ (hv 1)) (values_facts ρ a).2.2.1
    have hhead := apply_source_head ρ hv hh a
    have hm := congrArg (fun o => ordinalNaturalProduct o
      (ordinalNaturalSum (expressionValue ρ (hv 1)) (value1 ρ a))) he
    calc
      signedCNF (value1 ρ (.app source a)) = signedCNF
          (ordinalNaturalProduct (Ordinal.omega0^e.1.repr)
            (ordinalNaturalSum (expressionValue ρ (hv 1)) (value1 ρ a))) :=
        congrArg signedCNF (hhead.trans hm)
      _ = seedShift e.1.repr (signedCNF
          (ordinalNaturalSum (expressionValue ρ (hv 1)) (value1 ρ a))) :=
        principal_product_cnf e _ hb
      _ = seedShift e.1.repr
          (signedCNF (expressionValue ρ (hv 1))+signedCNF (value1 ρ a)) :=
        congrArg (seedShift e.1.repr) (cnf_sum _ _)
  have hz : ordinalNaturalSum e.1.repr 0=e.1.repr := by
    simpa only [Nat.cast_zero,add_zero] using actualNaturalSumFiniteRight e.1.repr 0
  have hone : seedShift e.1.repr (signedCNF 1)=signedCNF omega := by
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
      _ = signedCNF omega := congrArg signedCNF he.symm
  change signedCNF (value1 ρ (.app source unitPair.1))-
    signedCNF (value1 ρ (.app source unitPair.2))=(2^12 : Int) • signedCNF omega
  calc
    signedCNF (value1 ρ (.app source unitPair.1))-
        signedCNF (value1 ρ (.app source unitPair.2)) =
        seedShift e.1.repr (signedCNF (expressionValue ρ (hv 1))+signedCNF (value1 ρ unitPair.1))-
        seedShift e.1.repr (signedCNF (expressionValue ρ (hv 1))+signedCNF (value1 ρ unitPair.2)) :=
      congrArg₂ (fun a b : CantorGroup => a-b) (hscale unitPair.1) (hscale unitPair.2)
    _ = seedShift e.1.repr
        ((signedCNF (expressionValue ρ (hv 1))+signedCNF (value1 ρ unitPair.1))-
         (signedCNF (expressionValue ρ (hv 1))+signedCNF (value1 ρ unitPair.2))) :=
      (map_sub (seedShift e.1.repr) _ _).symm
    _ = seedShift e.1.repr (difference ρ unitPair) := by
      apply congrArg (seedShift e.1.repr)
      unfold difference
      abel
    _ = seedShift e.1.repr ((2^12 : Int) • signedCNF 1) :=
      congrArg (seedShift e.1.repr) (unit_difference ρ)
    _ = (2^12 : Int) • seedShift e.1.repr (signedCNF 1) :=
      (seedShift e.1.repr).map_zsmul (2^12 : Int) (signedCNF 1)
    _ = (2^12 : Int) • signedCNF omega := congrArg (fun a => (2^12 : Int) • a) hone

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.OmegaSeed.Proof
