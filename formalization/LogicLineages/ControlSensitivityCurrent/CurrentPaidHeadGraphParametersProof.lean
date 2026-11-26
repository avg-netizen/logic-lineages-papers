module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphPaymentProof
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphShiftProof
public import LogicLineages.ControlSensitivityCurrent.CurrentOrdinalEvaluationProof
public import LogicLineages.ControlSensitivityCurrent.CurrentAffineHeadsPositiveProof
public import LogicLineages.OrdinalComparison.GeneralOmegaHeadLimitProof
public import LogicLineages.OrdinalComparison.UnitHeadCodeProof
public import LogicLineages.OrdinalComparison.EncodedFiniteTailProof
public import LogicLineages.OrdinalComparison.RawNormCode
public import LogicLineages.PermittedControl.EncodedEvaluatorProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open AdmissibleSum AdmissibleAssignment ParametricSourceSuccessor ForwardTranslation

private theorem unitValue (f : Nat → Nat) {Γ} (e : OrdinalExpression Γ)
    (ν : OrdinalComponent Γ → Ordinal) :
    denoteWith f ν (UnitHeadEvaluation.unitSyntax e)=atUnits f e := by
  induction e with
  | var x | zero | one | omega => rfl
  | add a b ha hb | emul a b ha hb | collapse a b ha hb =>
    simp only [UnitHeadEvaluation.unitSyntax,denoteWith,atUnits] at *
    rw [ha,hb]

private theorem unitScalarCode (f : Nat → Nat) (hf : FullAddition.Targets.SourceGrowth f)
    {Γ} (q : OrdinalExpression Γ) (c : Nat) (hc : atUnits f q=(c : Ordinal)) :
    encodedFiniteValue (CurrentOrdinalEvaluation.evaluate f [] (UnitHeadCode.unitCode (OrdinalSyntax.typedCode q)))=c := by
  obtain ⟨a,ha,hr⟩ := CurrentOrdinalEvaluation.calibration f hf (OrdinalComponent Γ)
    OrdinalSyntax.componentCode (UnitHeadEvaluation.unitSyntax q) [] (fun _ => 0) (fun _ => rfl)
  rw [unitValue, hc] at hr
  rw [UnitHeadCode.Proof.unit_exact]
  change encodedFiniteValue (CurrentOrdinalEvaluation.evaluate f []
    (OrdinalSyntax.code OrdinalSyntax.componentCode (UnitHeadEvaluation.unitSyntax q))) = c
  rw [ha]
  have hfin := (encodedFiniteCorrect a).1.mpr (hr.symm ▸ Ordinal.natCast_lt_omega0 c)
  have he := (encodedFiniteCorrect a).2 hfin
  rw [hr] at he
  exact_mod_cast he

private theorem noteShift (a : NONote) (ha : Order.IsSuccLimit a.1.repr) (δ : Nat) :
    ∃ b : NONote, shiftCode (rawNoteEncode a.1) δ = rawNoteEncode b.1 ∧
      b.1.repr=shiftHead a.1.repr δ := by
  let w := ClosedPositive.omega.evaluate
  let n := NONote.ofNat δ
  let p := naturalProduct w n
  let b := naturalSum a p
  have hw : w.1.repr = Ordinal.omega0 := by simp [w,ClosedPositive.evaluate,ONote.repr]
  have hn : n.1.repr = (δ : Ordinal) := by
    change (ONote.ofNat δ).repr = (δ : Ordinal)
    exact ONote.repr_ofNat δ
  have hp : p.1.repr=Ordinal.omega0*(δ : Ordinal) := by
    rw [naturalProductDenotation w n,hw,hn,ParametricFiniteCollapseArgument.Proof.naturalProduct_omega_finite]
  have hb : b.1.repr=shiftHead a.1.repr δ := by
    rw [naturalSumDenotation a p,hp]
    exact sumOmegaTail a.1.repr (normalRepresentationSound a) ha δ
  refine ⟨b,?_,hb⟩
  unfold shiftCode CurrentOrdinalEvaluation.omegaCode
  rw [encodedNatNoteCorrect δ]
  change encodedNaturalSum (rawNoteEncode a.1)
    (encodedNaturalProduct (rawNoteEncode w.1) (rawNoteEncode n.1)) = rawNoteEncode b.1
  have hpCode : encodedNaturalProduct (rawNoteEncode w.1) (rawNoteEncode n.1) = rawNoteEncode p.1 :=
    encodedNaturalProductCorrect w.1 n.1
  have hbCode : encodedNaturalSum (rawNoteEncode a.1) (rawNoteEncode p.1) = rawNoteEncode b.1 :=
    encodedNaturalSumCorrect a.1 p.1
  rw [hpCode,hbCode]

private theorem norm_exact (a : NONote) : rawNormCode (rawNoteEncode a.1)=actualOrdinalNorm a.1.repr := by
  rw [rawNormCodeCorrect,actualOrdinalNorm_notationCorrespondence]

private theorem value_exact (f : Nat → Nat) (hf : FullAddition.Targets.SourceGrowth f)
    (a : NONote) (t : Nat) : valueCode f (rawNoteEncode a.1) t=J f a.1.repr t := by
  unfold valueCode J actualHeadInitial
  rw [norm_exact]
  let n := t-actualOrdinalNorm a.1.repr
  rw [(encodedFiniteTailCorrect a n).1]
  have hm := (FullAddition.completeAddition.2.2.2 f hf).1
  rw [PermittedControl.evaluator_source f hm hf.1 (finiteTail a n),(finiteTailCorrect a n).1]

theorem exactParameters : Targets.ExactParameters := by
  intro p f hc hf Γ K u hu δ
  have hg := generatedAt p K u hu
  obtain ⟨a,_,_,hcode,_,hval,_,_,_⟩ := UnitHeadCode.Proof.actualPositiveClassification Γ 1 (u 1) (hg 1) (by decide)
  obtain ⟨c,hcval₀⟩ := (GenericScalar.generatedPositiveFinite f Γ (fun _ => 0) 0 (u 0) (hg 0)).2 rfl
  have hcval : atUnits f (u 0) = (c : Ordinal) := by
    simpa only [atUnits,Nat.zero_add,Nat.cast_one] using hcval₀
  have hv := (CurrentAffineHeads.positiveNoCollapse Γ 1 (u 1) (by decide) (hg 1)).2 f (fun _ => 1)
  have hK : a.evaluate.1.repr=atUnits f (u 1) := hval.trans hv.symm
  let β := scalarHeadNote a
  have hβ := GeneralOmegaHeadLimit.Proof.actualClosedHeadCalibration a
  have hβv : β.1.repr=ordinalNaturalProduct Ordinal.omega0 (atUnits f (u 1)) := by
    rw [show β.1.repr=fixedHead a from hβ.1]
    unfold fixedHead
    rw [hK]
  have hβl : Order.IsSuccLimit β.1.repr := hβ.1.symm ▸ hβ.2.2.2.1
  obtain ⟨ξ,hshift,hξv⟩ := noteShift β hβl δ
  have hξ : ξ.1.repr = shiftHead (ordinalNaturalProduct Ordinal.omega0 (atUnits f (u 1))) δ :=
    hξv.trans (congrArg (fun a => shiftHead a δ) hβv)
  have hsyntax := (SyntaxCode.StatementChecks.typedCheckExact Γ (Ty.curriedGround 1)
    (SyntaxCode.encodeTerm K)).mpr ⟨K,rfl⟩
  have hassign : PolicyAssignment.assignmentCode p (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm K) =
      some (OrdinalSyntax.vectorCode u) := by
    rw [PolicyAssignmentSyntaxProof.literal p Γ _ K,hu] <;> rfl
  have hunit := unitScalarCode f hf (u 0) c hcval
  refine ⟨β,ξ,c,?_,hβv,hξ,hcval,?_,?_,?_⟩
  · have hindex : (Fin.succ (0 : Fin 1) : Fin 2) = 1 := by decide
    unfold parameterCode
    simp only [hsyntax,↓reduceIte,hassign,bind,Option.bind_some,OrdinalSyntax.vectorCode,
      List.ofFn_succ,List.getElem?_cons_zero,List.getElem?_cons_succ,hindex,hcode,pure,hunit,hβ.2.1,hshift,β] <;> rfl
  · rw [norm_exact,hβv]
  · rw [norm_exact,hξ]
  · intro t ht
    rw [value_exact f hf ξ t,hξ]

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
