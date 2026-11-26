module
public import LogicLineages.StandardControlCurrent.PolicyFiniteTargets
public import LogicLineages.StandardControlCurrent.PolicyLevelTwoProof
public import LogicLineages.OrdinalComparison.WWSourceFinitePositiveProof
public import LogicLineages.OrdinalComparison.WWSourceAssignmentProfileProof
public import LogicLineages.OrdinalComparison.WWSourcePolynomialArithmeticProof
public import LogicLineages.OrdinalComparison.RawComparisonProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyFiniteProof
open OrdinalComparison Source Source.ForwardTranslation Source.SourceClasses Source.AdmissibleSum
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LevelTwoCounterexample

private theorem check_add (a b : Nat) : PolicyFinite.finiteScalarCode (4*Nat.pair a b+2)=
    (PolicyFinite.finiteScalarCode a && PolicyFinite.finiteScalarCode b) := by
  have hm : (4*Nat.pair a b+2)%4=2 := by omega
  have hd : (4*Nat.pair a b+2)/4=Nat.pair a b := by omega
  rw [PolicyFinite.finiteScalarCode]
  simp [hm,hd]
private theorem check_shift (h a : Nat) : PolicyFinite.finiteScalarCode (4*Nat.pair h a+3)=
    (decide (rawComparisonCode (encodedClosedPositive h) (rawNoteEncode (.oadd 1 1 .zero))=0) &&
      PolicyFinite.finiteScalarCode a) := by
  have hm : (4*Nat.pair h a+3)%4=3 := by omega
  have hd : (4*Nat.pair h a+3)/4=Nat.pair h a := by omega
  rw [PolicyFinite.finiteScalarCode]
  simp [hm,hd]

theorem check_exact (ι : Type) (index : ι → Nat) (s : Scalar ι) :
    PolicyFinite.finiteScalarCode (scalarSyntaxCode index s)=true ↔ PolicyFinite.FiniteScalar s := by
  induction s with
  | one => simp [scalarSyntaxCode,PolicyFinite.finiteScalarCode,PolicyFinite.FiniteScalar,scalarHeads]
  | var x =>
    have hm : (4*index x+1)%4=1 := by omega
    simp [scalarSyntaxCode,PolicyFinite.finiteScalarCode,hm,PolicyFinite.FiniteScalar,scalarHeads]
  | add a b iha ihb =>
    simp only [scalarSyntaxCode,check_add,Bool.and_eq_true_iff,iha,ihb,
      PolicyFinite.FiniteScalar,scalarHeads,List.mem_append,or_imp,forall_and]
  | shift c a ih =>
    rw [scalarSyntaxCode,check_shift,Bool.and_eq_true_iff,decide_eq_true_eq,
      encodedClosedPositiveCorrect c,ih]
    let w : NONote := ClosedPositive.omega.evaluate
    have hw : w.1.repr=Ordinal.omega0 := by simp [w,ClosedPositive.evaluate,ONote.repr]
    have he := (rawComparisonOrdinalCorrect c.evaluate w).1
    change (rawComparisonCode (rawNoteEncode c.evaluate.1) (rawNoteEncode w.1)=0 ∧ _) ↔ _
    rw [he,hw]
    simp only [PolicyFinite.FiniteScalar,scalarHeads,List.mem_cons,forall_eq_or_imp]

theorem finite_polynomial {ι : Type} (s : Scalar ι) (hs : PolicyFinite.FiniteScalar s) : PolynomialScalar s := by
  intro c hc
  have hh := GeneralOmegaHeadLimit.Proof.actualClosedHeadCalibration c
  have hω : Ordinal.omega0 < Ordinal.omega0^Ordinal.omega0 := by
    simpa only [Ordinal.opow_one] using
      (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr Ordinal.one_lt_omega0
  exact ⟨hh.2.2.2.1,sourceNaturalProductPolynomialClosure _ _ hω ((hs c hc).trans hω)⟩

private theorem extracted_noOmega_finite {Γ : List Ty} (t : OrdinalExpression Γ) (c : ClosedPositive)
    (he : extractPositive t=some c) (hn : noOmega t=true) : ∃ n, finitePositiveValue t=some n := by
  induction t generalizing c with
  | var x => simp [extractPositive] at he
  | zero => simp [extractPositive] at he
  | collapse a b iha ihb => simp [extractPositive] at he
  | one => exact ⟨1,rfl⟩
  | omega => simp [noOmega] at hn
  | add a b iha ihb =>
    obtain ⟨ca,ha,cb,hb,hc⟩ : ∃ ca,extractPositive a=some ca ∧ ∃ cb,extractPositive b=some cb ∧ ClosedPositive.add ca cb=c := by
      simpa only [extractPositive,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] using he
    have hno : noOmega a=true ∧ noOmega b=true := Bool.and_eq_true_iff.mp hn
    obtain ⟨na,hna⟩ := iha ca ha hno.1
    obtain ⟨nb,hnb⟩ := ihb cb hb hno.2
    exact ⟨na+nb,by simp [finitePositiveValue,hna,hnb]⟩
  | emul a b iha ihb =>
    obtain ⟨ca,ha,cb,hb,hc⟩ : ∃ ca,extractPositive a=some ca ∧ ∃ cb,extractPositive b=some cb ∧ ClosedPositive.emul ca cb=c := by
      simpa only [extractPositive,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] using he
    have hno : noOmega a=true ∧ noOmega b=true := Bool.and_eq_true_iff.mp hn
    obtain ⟨na,hna⟩ := iha ca ha hno.1
    obtain ⟨nb,hnb⟩ := ihb cb hb hno.2
    exact ⟨2^na*nb,by simp [finitePositiveValue,hna,hnb]⟩

theorem noOmega_scalar {Γ : List Ty} (t : OrdinalExpression Γ)
    (s : Scalar (OrdinalComponent Γ)) (he : compileScalar t=some s) (hn : noOmega t=true) :
    PolicyFinite.FiniteScalar s := by
  induction t generalizing s with
  | var x => cases Option.some.inj he; simp [PolicyFinite.FiniteScalar,scalarHeads]
  | one => cases Option.some.inj he; simp [PolicyFinite.FiniteScalar,scalarHeads]
  | zero => simp [compileScalar] at he
  | omega => simp [compileScalar] at he
  | emul a b iha ihb => simp [compileScalar] at he
  | add a b iha ihb =>
    obtain ⟨ca,ha,cb,hb,hc⟩ : ∃ ca,compileScalar a=some ca ∧ ∃ cb,compileScalar b=some cb ∧ Scalar.add ca cb=s := by
      simpa only [compileScalar,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] using he
    subst s
    have hno : noOmega a=true ∧ noOmega b=true := Bool.and_eq_true_iff.mp hn
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact iha ca ha hno.1 c h
    · exact ihb cb hb hno.2 c h
  | collapse a b iha ihb =>
    obtain ⟨ca,ha,cb,hb,hc⟩ : ∃ ca,extractPositive a=some ca ∧ ∃ cb,compileScalar b=some cb ∧ Scalar.shift ca cb=s := by
      simpa only [compileScalar,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] using he
    subst s
    have hno : noOmega a=true ∧ noOmega b=true := Bool.and_eq_true_iff.mp hn
    intro c hc
    rcases List.mem_cons.mp hc with h | h
    · subst c
      obtain ⟨n,hv⟩ := extracted_noOmega_finite a ca ha hno.1
      have hval := (finitePositiveValueSound Γ a n hv).2 (fun _ => 0)
      have hca := closedPositiveEvaluationSound Γ a ca ha (fun _ => 0)
      rw [hval] at hca
      rw [hca]
      exact Ordinal.natCast_lt_omega0 n
    · exact ihb cb hb hno.2 c h

theorem recursor_free : PolicyFiniteTargets.RecursorFreeClass := by
  intro p Γ hΓ τ t ht
  obtain ⟨v,hv,c,hc,_⟩ := actualSourceVectorCompilation Γ hΓ τ p t
  obtain ⟨w,hw,hn⟩ := actualRecursorFreeAssignmentNoOmega Γ τ p t ht
  have he : w=v := Option.some.inj (hw.symm.trans hv)
  subst w
  have hs := LevelTwoDecisionCompletion.MetadataProof.compiled_scalar v c hc
  exact ⟨v,c.scalar,hv,hs,noOmega_scalar (v 0) c.scalar hs (hn 0)⟩
end LogicLineages.StandardControlCurrent.PolicyFiniteProof
