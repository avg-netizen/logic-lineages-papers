module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowArithmeticEvaluation
public import LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowClosedTermCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticEvaluationProof
open GorbowSyntax GorbowStandardInstances GorbowSortedSyntaxCode GorbowArithmeticEvaluation

theorem stackCalibration : Comparators.GorbowArithmeticEvaluation.StackCalibration := by
  intro t
  induction t with
  | var i => exact Fin.elim0 i
  | zero => intro _ I stack; simp [run,GorbowTermPrefixCode.encode,step,Term.realize]
  | succ t ih =>
    intro ht I stack
    cases ht with | succ ht =>
      have h := ih ht I stack
      simp only [run] at h ⊢
      simp only [GorbowTermPrefixCode.encode,List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]
      rw [h]
      simp [step,Term.realize]
  | add t u iht ihu =>
    intro ht I stack
    cases ht with | add ht hu =>
      have hu' := ihu hu I stack
      have ht' := iht ht I (u.realize I Fin.elim0::stack)
      simp only [run] at hu' ht' ⊢
      simp only [GorbowTermPrefixCode.encode,List.reverse_cons,List.reverse_append,List.foldl_append,List.foldl_cons,List.foldl_nil]
      rw [hu',ht']
      simp [step,Term.realize]
  | mul t u iht ihu =>
    intro ht I stack
    cases ht with | mul ht hu =>
      have hu' := ihu hu I stack
      have ht' := iht ht I (u.realize I Fin.elim0::stack)
      simp only [run] at hu' ht' ⊢
      simp only [GorbowTermPrefixCode.encode,List.reverse_cons,List.reverse_append,List.foldl_append,List.foldl_cons,List.foldl_nil]
      rw [hu',ht']
      simp [step,Term.realize]
  | universalFunction t ih => intro h; cases h

private theorem rawAt (t : Term 0) (ht : ArithmeticTerm t) I :
    rawValue (GorbowTermPrefixCode.encode t)=some (t.realize I Fin.elim0) := by
  have hg := (GorbowClosedTermCodeProof.exactRawArithmetic _).mpr ⟨t,rfl,ht⟩
  simp [rawValue,hg,stackCalibration t ht I []]

theorem exactRawOutput : Comparators.GorbowArithmeticEvaluation.ExactRawOutput := by
  intro raw value I
  constructor
  · intro h
    have hg : GorbowClosedTermCode.arithmeticRaw raw=true := by
      cases he : GorbowClosedTermCode.arithmeticRaw raw <;> simp_all [rawValue]
    obtain ⟨t,rfl,ht⟩ := (GorbowClosedTermCodeProof.exactRawArithmetic raw).mp hg
    have hv := rawAt t ht I
    exact ⟨t,rfl,ht,Option.some.inj (h.symm.trans hv)⟩
  · rintro ⟨t,rfl,ht,rfl⟩
    exact rawAt t ht I

private theorem sortedAt (t : Term 0) (ht : ArithmeticTerm t) I :
    sortedValue (termCode t)=some (t.realize I Fin.elim0) := by
  simp [sortedValue,(GorbowSortedSyntaxCodeProof.actualCalibration.2.2.1 0 t),rawAt t ht I]

theorem exactSortedOutput : Comparators.GorbowArithmeticEvaluation.ExactSortedOutput := by
  intro code value I
  constructor
  · intro h
    cases hd : decodeTermRaw code with
    | none => simp [sortedValue,hd] at h
    | some raw =>
      have hr : rawValue raw=some value := by simpa [sortedValue,hd] using h
      obtain ⟨t,he,ht,hv⟩ := (exactRawOutput raw value I).mp hr
      have hc := (GorbowSortedSyntaxCodeProof.exactRawDecoding.2 code raw).mp hd
      exact ⟨t,by simpa [he,termRawNumber,termCode,GorbowCodeConstructors.termNumber] using hc,ht,hv⟩
  · rintro ⟨t,rfl,ht,rfl⟩
    exact sortedAt t ht I

theorem exactRejection : Comparators.GorbowArithmeticEvaluation.ExactRejection := by
  constructor
  · intro raw
    constructor
    · intro h
      cases hg : GorbowClosedTermCode.arithmeticRaw raw with
      | false => rfl
      | true =>
        obtain ⟨t,he,ht⟩ := (GorbowClosedTermCodeProof.exactRawArithmetic raw).mp hg
        have hv := rawAt t ht (GorbowRevisionSemantics.interpretation ⟨fun _ => False,fun _ => 0⟩ (fun _ => False))
        rw [←he,h] at hv
        contradiction
    · intro hg; simp [rawValue,hg]
  · intro code
    constructor
    · intro h
      cases hg : GorbowSortedBooleanCode.arithmeticTermCode code with
      | false => rfl
      | true =>
        obtain ⟨t,rfl,ht⟩ := (GorbowSortedBooleanCodeProof.exactDomains.2.2 code).mp hg
        have hv := sortedAt t ht (GorbowRevisionSemantics.interpretation ⟨fun _ => False,fun _ => 0⟩ (fun _ => False))
        rw [h] at hv
        contradiction
    · intro hg
      cases hv : sortedValue code with
      | none => rfl
      | some value =>
        obtain ⟨t,rfl,ht,_⟩ := (exactSortedOutput code value
          (GorbowRevisionSemantics.interpretation ⟨fun _ => False,fun _ => 0⟩ (fun _ => False))).mp hv
        have hh := (GorbowSortedBooleanCodeProof.exactDomains.2.2 _).mpr ⟨t,rfl,ht⟩
        rw [hg] at hh
        contradiction

theorem numeralCalibration : Comparators.GorbowArithmeticEvaluation.NumeralCalibration := by
  intro n
  simpa [numeral_realize] using sortedAt (Term.numeral n)
    (GorbowStandardInstancesProof.arithmeticNumerals 0 n)
    (GorbowRevisionSemantics.interpretation ⟨fun _ => False,fun _ => 0⟩ (fun _ => False))

private theorem pr_apply : Primrec (fun p : Nat × List Nat =>
    if p.1=1 then some (0::p.2)
    else if p.1=2 then if p.2.length≥1 then some ((p.2.getD 0 0+1)::p.2.drop 1) else none
    else if p.1=3 then if p.2.length≥2 then some ((p.2.getD 0 0+p.2.getD 1 0)::p.2.drop 2) else none
    else if p.1=4 then if p.2.length≥2 then some ((p.2.getD 0 0*p.2.getD 1 0)::p.2.drop 2) else none
    else none) := by
  have hg (i : Nat) : Primrec (fun p : Nat × List Nat => p.2.getD i 0) :=
    (Primrec.list_getD 0).comp Primrec.snd (Primrec.const i)
  have hd (i : Nat) : Primrec (fun p : Nat × List Nat => p.2.drop i) :=
    Primrec.list_drop.comp (Primrec.const i) Primrec.snd
  have hl (i : Nat) : PrimrecPred (fun p : Nat × List Nat => i≤p.2.length) :=
    Primrec.nat_le.comp (Primrec.const i) (Primrec.list_length.comp Primrec.snd)
  have ht (i : Nat) : PrimrecPred (fun p : Nat × List Nat => p.1=i) :=
    Primrec.eq.comp Primrec.fst (Primrec.const i)
  have hz := Primrec.option_some.comp (Primrec.list_cons.comp (Primrec.const 0) (Primrec.snd : Primrec (fun p : Nat × List Nat => p.2)))
  have hs := Primrec.ite (hl 1) (Primrec.option_some.comp (Primrec.list_cons.comp
    (Primrec.nat_add.comp (hg 0) (Primrec.const 1)) (hd 1))) (Primrec.const none)
  have ha := Primrec.ite (hl 2) (Primrec.option_some.comp (Primrec.list_cons.comp
    (Primrec.nat_add.comp (hg 0) (hg 1)) (hd 2))) (Primrec.const none)
  have hm := Primrec.ite (hl 2) (Primrec.option_some.comp (Primrec.list_cons.comp
    (Primrec.nat_mul.comp (hg 0) (hg 1)) (hd 2))) (Primrec.const none)
  exact Primrec.ite (ht 1) hz (Primrec.ite (ht 2) hs (Primrec.ite (ht 3) ha (Primrec.ite (ht 4) hm (Primrec.const none))))
private theorem pr_step : Primrec (fun p : Option (List Nat) × Nat => step p.1 p.2) := by
  have ht : Primrec (fun p : (Option (List Nat) × Nat) × List Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  have hf := pr_apply.comp (ht.pair Primrec.snd)
  exact Primrec.option_bind Primrec.fst hf.to₂
private theorem pr_run : Primrec (fun p : List Nat × List Nat => run p.1 p.2) := by
  have hs : Primrec (fun p : (List Nat × List Nat) × Option (List Nat) × Nat => step p.2.1 p.2.2) :=
    pr_step.comp Primrec.snd
  exact Primrec.list_foldl (Primrec.list_reverse.comp Primrec.fst) (Primrec.option_some.comp Primrec.snd) hs.to₂
private theorem pr_value : Primrec (fun stack : List Nat => if stack.length=1 then some (stack.getD 0 0) else none) :=
  Primrec.ite (Primrec.eq.comp Primrec.list_length (Primrec.const 1))
    (Primrec.option_some.comp ((Primrec.list_getD 0).comp Primrec.id (Primrec.const 0))) (Primrec.const none)
private theorem pr_raw : Primrec rawValue := by
  have hr := pr_run.comp (Primrec.id.pair (Primrec.const []))
  have hb := Primrec.option_bind hr (pr_value.comp Primrec.snd).to₂
  exact Primrec.ite (Primrec.eq.comp GorbowClosedTermCodeProof.uniformPrograms.1 (Primrec.const true)) hb (Primrec.const none)
private theorem pr_sorted : Primrec sortedValue :=
  Primrec.option_bind GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.2.2.2.2.1 (pr_raw.comp Primrec.snd).to₂

theorem uniformPrograms : Comparators.GorbowArithmeticEvaluation.UniformPrograms :=
  ⟨pr_step,pr_run,pr_raw,pr_sorted⟩
theorem gorbowArithmeticEvaluation : Comparators.GorbowArithmeticEvaluation.Target :=
  ⟨stackCalibration,exactRawOutput,exactSortedOutput,exactRejection,numeralCalibration,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowArithmeticEvaluationProof
