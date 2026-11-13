module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HistoryMachine.NativeProgramsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HistoryMachine.NativeProof
open GorbowPRProgram GorbowPublishedDCB GorbowProofChecker List.Vector

theorem iteratorCalibration : Targets.IteratorCalibration := by
  intro kernel hk state index fuel count
  have hkernel (st : State) :
      evaluate kernel (Encodable.encode st ::ᵥ index ::ᵥ fuel ::ᵥ nil) =
        Encodable.encode (transition index fuel st) := by
    have h := hk (Encodable.encode st ::ᵥ index ::ᵥ fuel ::ᵥ nil)
    change evaluate kernel (Encodable.encode st ::ᵥ index ::ᵥ fuel ::ᵥ nil) =
      Encodable.encode (transition index fuel (decodedState (Encodable.encode st))) at h
    simpa only [decodedState,Encodable.encodek,Option.getD_some] using h
  induction count with
  | zero => rfl
  | succ count ih =>
      change evaluate kernel
        (evaluate (iterator kernel) (count ::ᵥ Encodable.encode state ::ᵥ index ::ᵥ fuel ::ᵥ nil) ::ᵥ
          index ::ᵥ fuel ::ᵥ nil) = _
      rw [ih,hkernel,Function.iterate_succ_apply']

private theorem emptyIteration (index fuel : Nat) (state : Option History) (count : Nat) :
    (transition index fuel)^[count] (state,[]) = (state,[]) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply]
      exact ih

theorem originalHistoryRun : Targets.OriginalHistoryRun := by
  intro index fuel state lines
  induction lines generalizing state with
  | nil => intro count _; exact emptyIteration index fuel state count
  | cons line lines ih =>
      intro count hcount
      cases count with
      | zero => simp only [List.length_cons] at hcount; omega
      | succ count =>
          rw [Function.iterate_succ_apply]
          change (transition index fuel)^[count]
            (GorbowTheoryChecker.step
              (GorbowEnumeratedProvability.axiomCheck (Denumerable.ofNat Code index,fuel)) state line,lines) = _
          exact ih _ count (Nat.le_of_succ_le_succ hcount)

private theorem finishOriginal (index fuel context formula cert : Nat) :
    finish ((decodedLines cert).foldl (GorbowTheoryChecker.step
      (GorbowEnumeratedProvability.axiomCheck (Denumerable.ofNat Code index,fuel))) (some []),[])
      context formula cert =
    GorbowEnumeratedProvability.check (Denumerable.ofNat Code index,fuel) context formula cert := by
  cases hf : GorbowSortedSyntaxCode.decodeFormulaRaw formula with
  | none => simp only [finish,hf,GorbowEnumeratedProvability.check,GorbowTheoryNumericCertificate.check]
  | some raw =>
      cases hc : GorbowNumericCertificate.decodeCertificate cert with
      | none => simp only [finish,hf,hc,GorbowEnumeratedProvability.check,GorbowTheoryNumericCertificate.check]
      | some lines =>
          simp only [finish,hf,hc,decodedLines,Option.getD_some,GorbowEnumeratedProvability.check,
            GorbowTheoryNumericCertificate.check,GorbowTheoryChecker.verifies,
            GorbowTheoryChecker.checkProof,GorbowTheoryChecker.run]
          cases hh : lines.foldl (GorbowTheoryChecker.step
              (GorbowEnumeratedProvability.axiomCheck (Denumerable.ofNat Code index,fuel))) (some []) with
          | none => rfl
          | some history => cases history <;> rfl

theorem sameNumericChecker : Targets.SameNumericChecker := by
  intro kernel bound initial finalizer hk hb hi hz c fuel context formula cert
  have hfinal (st : State) :
      evaluate finalizer (Encodable.encode st ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil) =
        if finish st context formula cert then 1 else 0 := by
    have h := hz (Encodable.encode st ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil)
    change evaluate finalizer (Encodable.encode st ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil) =
      (if finish (decodedState (Encodable.encode st)) context formula cert then 1 else 0) at h
    simpa only [decodedState,Encodable.encodek,Option.getD_some] using h
  have hbound : evaluate bound (cert ::ᵥ nil) = Encodable.encode (decodedLines cert) := hb _
  have hinitial : evaluate initial (cert ::ᵥ nil) =
      Encodable.encode ((some [],decodedLines cert) : State) := hi _
  change evaluate finalizer
    (evaluate (iterator kernel)
      (evaluate bound (cert ::ᵥ nil) ::ᵥ evaluate initial (cert ::ᵥ nil) ::ᵥ
        Encodable.encode c ::ᵥ fuel ::ᵥ nil) ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil) = _
  rw [hbound,hinitial,iteratorCalibration kernel hk]
  have ht := originalHistoryRun (Encodable.encode c) fuel (some []) (decodedLines cert)
    (Encodable.encode (decodedLines cert)) (Encodable.length_le_encode _)
  rw [ht,hfinal,finishOriginal,Denumerable.ofNat_encode]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HistoryMachine.NativeProof
