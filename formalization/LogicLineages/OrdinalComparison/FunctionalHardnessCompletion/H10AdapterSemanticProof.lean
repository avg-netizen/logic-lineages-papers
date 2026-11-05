module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10AdapterTargets
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitBridgeRowsProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitNumericCalibrationProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10ValidityCalibrationProof
public import LogicLineages.ComputabilityKnowledge.PolynomialDomainShiftProof
public import LogicLineages.ComputabilityKnowledge.PolynomialCircuitEffectivityProof
public import LogicLineages.ComputabilityKnowledge.PolynomialCircuitProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Adapter.Proof
open LogicLineages.ComputabilityKnowledge
open PolynomialCircuit PolynomialDomainShift CircuitLinear Narendran
open PositiveExpression

theorem impossibleSystemCorrect : Targets.ImpossibleSystemCorrect := by
  have hw : WellFormedCode impossibleSystem := by
    intro row hr m hm i hi
    have hr' : row=[(1,0,none)] := List.mem_singleton.mp hr
    subst row
    have hm' : m=(1,0,none) := List.mem_singleton.mp hm
    subst m
    cases hi
  refine ⟨hw,?_⟩
  rintro ⟨c,hc,hcw,hsol⟩
  have he : impossibleSystem=c :=
    Option.some.inj ((Encodable.encodek impossibleSystem).symm.trans hc)
  subst c
  obtain ⟨p,hp⟩ := (CircuitLinear.Proof.raw_system_faithful impossibleSystem hw).mp hsol
  have hh := hp [(1,0,none)] (by simp [impossibleSystem])
  norm_num [rowPolynomial,monomialPolynomial] at hh

theorem originalSafety : Targets.OriginalSafety := by
  intro xs h
  simp [translate,h]

theorem parsedCalibration : Targets.ParsedCalibration := by
  intro xs p hdec hp
  have hv := (H10Validity.Proof.inputValidity xs).mpr ⟨p,hdec,hp⟩
  have hs : encodedShift xs=some (PolynomialCircuit.encode (shift p)) := by
    simp [encodedShift,hdec]
  have hc := PolynomialCircuitEffectivityProof.codeCorrespondence (shift p)
  have hn := CircuitNumeric.Proof.encoderCalibration (PolynomialCircuit.compile (shift p))
  simp [translate,hv,hs,hc,hn]

private theorem variable_eval_agree (vs : List Nat) (r s : Nat → Int)
    (h : ∀ i∈vs, r i=s i) :
    MvPolynomial.eval r (variableProduct vs)=MvPolynomial.eval s (variableProduct vs) := by
  induction vs with
  | nil => simp [variableProduct,interpretTerms]
  | cons i vs ih =>
    simp only [variableProduct,MvPolynomial.eval_mul,MvPolynomial.eval_X]
    rw [h i (List.mem_cons_self),ih (fun j hj => h j (List.mem_cons_of_mem i hj))]

private theorem terms_eval_agree (ms : Monomials) (r s : Nat → Int)
    (h : ∀ m∈ms,∀ i∈m.2,r i=s i) :
    MvPolynomial.eval r (interpretTerms ms)=MvPolynomial.eval s (interpretTerms ms) := by
  induction ms with
  | nil => simp [variableProduct,interpretTerms]
  | cons m ms ih =>
    rcases m with ⟨z,vs⟩
    simp only [interpretTerms,MvPolynomial.eval_add,MvPolynomial.eval_mul,MvPolynomial.eval_C]
    rw [variable_eval_agree vs r s (h _ List.mem_cons_self),
      ih (fun m hm => h m (List.mem_cons_of_mem _ hm))]

private theorem code_eval_agree (p : PolynomialCircuit.Code) (hp : p.WellFormed)
    (r s : Nat → Int) (h : ∀ i, i < p.inputCount → r i = s i) :
    MvPolynomial.eval r (interpret p)=MvPolynomial.eval s (interpret p) :=
  terms_eval_agree p.monomials r s (fun m hm i hi => h i (hp m hm i hi))

/-- The original finite natural witnesses include zero. Shifting precedes the
positive circuit compiler, and only original valid references determine roots. -/
theorem polynomialCircuitRoot : Targets.PolynomialCircuitRoot := by
  intro p hp
  have hw := PolynomialDomainShiftProof.wellFormedPreserved p hp
  rw [PolynomialDomainShiftProof.rootEquivalence p hp]
  constructor
  · rintro ⟨ν,hν⟩
    exact ⟨CircuitComparison.finiteVal ν,
      (PolynomialCircuitProof.zeroIff (shift p) hw (CircuitComparison.finiteVal ν)).mp hν⟩
  · rintro ⟨ρ,hρ⟩
    have hz := (PolynomialCircuitProof.zeroIff (shift p) hw ρ).mpr hρ
    let ν : Fin (shift p).inputCount → PosNat := fun i => ρ i.val
    refine ⟨ν,?_⟩
    change MvPolynomial.eval (fun i => ((CircuitComparison.finiteVal ν i).val : Int))
      (interpret (shift p))=0
    rw [code_eval_agree (shift p) hw _ (fun i => ((ρ i).val : Int)) ?_]
    · exact hz
    · intro i hi
      simp [CircuitComparison.finiteVal,ν,hi]

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Adapter.Proof
