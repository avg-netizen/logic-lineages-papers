module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowLiftedDictionary
public import LogicLineages.ComputabilityKnowledge.GorbowTermShiftCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowLiftedDictionaryProof
open GorbowSyntax GorbowSyntaxValidation GorbowTermShiftCode GorbowLiftedDictionary

private theorem shiftZero {n : Nat} (t : Term n) : shiftTerm 0 t = t := by
  exact GorbowSubstitution.substitute_variables t

private theorem succShift {n : Nat} (b : Nat) (t : Term n) :
    GorbowFormulaSubstitution.renameTerm Fin.succ (shiftTerm b t) = shiftTerm (b+1) t := by
  unfold shiftTerm GorbowFormulaSubstitution.renameTerm
  rw [GorbowSubstitution.substitute_composition]
  rfl

theorem boundIndex : Comparators.GorbowLiftedDictionary.BoundIndex := by
  intro n m b σ
  induction b with
  | zero => intro i h; omega
  | succ b ih =>
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro h; rfl
      · intro h
        have hj : j.val < b := by simpa only [Fin.val_succ, Nat.add_lt_add_iff_right] using h
        simp only [liftN, GorbowFormulaSubstitution.liftSubstitute, Fin.cases_succ]
        rw [ih j hj]
        rfl

theorem freeIndex : Comparators.GorbowLiftedDictionary.FreeIndex := by
  intro n m b σ
  induction b with
  | zero =>
      intro i h
      simp only [liftN, Nat.sub_zero, shiftZero]
      congr 1
  | succ b ih =>
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro h; simp only [Fin.val_zero] at h; omega
      · intro h
        have hj : b ≤ j.val := by simpa only [Fin.val_succ, Nat.add_le_add_iff_right] using h
        simp only [liftN, GorbowFormulaSubstitution.liftSubstitute, Fin.cases_succ]
        rw [ih j hj, succShift]
        congr 2
        apply Fin.ext
        simp only [Fin.val_succ, Nat.add_sub_add_right]

private theorem validEncode (n : Nat) (t : Term n) : validTerm n (GorbowTermPrefixCode.encode t) = true :=
  (GorbowSyntaxValidationProof.exactTypedDomain.1 n _).mpr
    ⟨t, (GorbowTermPrefixCodeProof.decoderExact n _ t).mpr rfl⟩

theorem dictionaryCalibration : Comparators.GorbowLiftedDictionary.DictionaryCalibration := by
  intro n m σ
  refine ⟨by simp [dictionary], ?_, ?_⟩
  · simp [dictionaryValid, dictionary, List.all_eq_true, validEncode]
  · intro i
    simp [dictionary, List.getD_eq_getElem?_getD, i.isLt]

theorem exactDictionaryDomain : Comparators.GorbowLiftedDictionary.ExactDictionaryDomain := by
  intro n m dict
  constructor
  · intro h
    have hh : dict.length = n ∧ dict.all (fun raw => validTerm m raw) = true := by
      simpa only [dictionaryValid, Bool.and_eq_true, decide_eq_true_eq] using h
    have hl : dict.length = n := hh.1
    have ha : ∀ raw ∈ dict, validTerm m raw = true := List.all_eq_true.mp hh.2
    have hex : ∀ i : Fin n, ∃ t : Term m, dict[i.val]'(by omega) = GorbowTermPrefixCode.encode t := by
      intro i
      have hv := ha (dict[i.val]'(by omega)) (List.getElem_mem _)
      obtain ⟨t,ht⟩ := (GorbowSyntaxValidationProof.exactTypedDomain.1 m _).mp hv
      exact ⟨t,(GorbowTermPrefixCodeProof.decoderExact m _ t).mp ht⟩
    choose σ hσ using hex
    refine ⟨σ,?_⟩
    apply List.ext_getElem
    · simp [dictionary,hl]
    · intro i hi hj
      simpa [dictionary] using hσ ⟨i,by omega⟩
  · rintro ⟨σ,rfl⟩
    exact (dictionaryCalibration n m σ).2.1

theorem liftedCodeCalibration : Comparators.GorbowLiftedDictionary.LiftedCodeCalibration := by
  intro n m b σ i
  by_cases hi : i.val < b
  · rw [boundIndex n m b σ i hi]
    simp [liftedCode,hi,GorbowTermPrefixCode.encode]
  · have hb : b ≤ i.val := by omega
    rw [freeIndex n m b σ i hb]
    have hj : i.val-b < n := by omega
    rw [liftedCode, if_neg hi, (dictionaryCalibration n m σ).2.2 ⟨i.val-b,hj⟩]
    simpa [shiftRaw] using congrArg Prod.snd
      (GorbowTermShiftCodeProof.scannerInvariant m b (σ ⟨i.val-b,hj⟩) [] [])

private theorem pr_allValid : Primrec (fun p : Nat × List (List Nat) => p.2.all (fun raw => validTerm p.1 raw)) := by
  have hp : PrimrecRel (fun raw : List Nat => fun m : Nat => validTerm m raw = true) :=
    Primrec.eq.comp (GorbowSyntaxValidationProof.uniformPrograms.2.2.2.1.comp (Primrec.snd.pair Primrec.fst)) (Primrec.const true)
  have h := hp.forall_mem_list.decide.comp Primrec.snd Primrec.fst
  apply h.of_eq
  intro p
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, List.all_eq_true]

private theorem pr_dictionaryValid : Primrec (fun p : Nat × Nat × List (List Nat) => dictionaryValid p.1 p.2.1 p.2.2) :=
  Primrec.and.comp
    (Primrec.eq.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst).decide
    (pr_allValid.comp Primrec.snd)

private theorem pr_liftedCode : Primrec (fun p : Nat × Nat × List (List Nat) × Nat => liftedCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hm : Primrec (fun p : Nat × Nat × List (List Nat) × Nat => p.1) := Primrec.fst
  have hb : Primrec (fun p : Nat × Nat × List (List Nat) × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : Nat × Nat × List (List Nat) × Nat => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hi : Primrec (fun p : Nat × Nat × List (List Nat) × Nat => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hget := (Primrec.list_getD ([] : List Nat)).comp hd (Primrec.nat_sub.comp hi hb)
  exact Primrec.ite (Primrec.nat_lt.comp hi hb)
    (Primrec.list_cons.comp (Primrec.const 0) (Primrec.list_cons.comp hi (Primrec.const [])))
    (GorbowTermShiftCodeProof.uniformPrograms.2.2.1.comp (hm.pair (hb.pair hget)))

theorem uniformPrograms : Comparators.GorbowLiftedDictionary.UniformPrograms := ⟨pr_dictionaryValid,pr_liftedCode⟩

theorem gorbowLiftedDictionary : Comparators.GorbowLiftedDictionary.Target :=
  ⟨boundIndex,freeIndex,dictionaryCalibration,exactDictionaryDomain,liftedCodeCalibration,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowLiftedDictionaryProof
