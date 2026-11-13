module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HistoryMachine.NativeProgramsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HistoryMachine.NativeProof
open GorbowPRProgram GorbowPublishedDCB GorbowProofChecker List.Vector

theorem iteratorCalibration : Targets.IteratorCalibration := by
  intro kernel hk state index fuel count
  induction count with
  | zero => rfl
  | succ count ih =>
      change evaluate kernel
        (evaluate (iterator kernel) (count ::ᵥ Encodable.encode state ::ᵥ index ::ᵥ fuel ::ᵥ nil) ::ᵥ
          index ::ᵥ fuel ::ᵥ nil) = _
      rw [ih,hk]
      simp only [kernelFunction,decodedState,Encodable.encodek,Option.getD_some]
      rw [Function.iterate_succ_apply']

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
  cases hf : GorbowSortedSyntaxCode.decodeFormulaRaw formula <;>
    cases hc : GorbowNumericCertificate.decodeCertificate cert <;>
    simp only [finish,hf,hc,decodedLines,Option.getD_some,GorbowEnumeratedProvability.check,
      GorbowTheoryNumericCertificate.check,GorbowTheoryChecker.verifies,
      GorbowTheoryChecker.checkProof,GorbowTheoryChecker.run]

theorem sameNumericChecker : Targets.SameNumericChecker := by
  intro kernel bound initial finalizer hk hb hi hz c fuel context formula cert
  have hbound : evaluate bound (cert ::ᵥ nil) = Encodable.encode (decodedLines cert) := hb _
  have hinitial : evaluate initial (cert ::ᵥ nil) =
      Encodable.encode ((some [],decodedLines cert) : State) := hi _
  change evaluate finalizer
    (evaluate (iterator kernel)
      (evaluate bound (cert ::ᵥ nil) ::ᵥ evaluate initial (cert ::ᵥ nil) ::ᵥ
        Encodable.encode c ::ᵥ fuel ::ᵥ nil) ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil) = _
  rw [hbound,hinitial,iteratorCalibration kernel hk]
  have ht := originalHistoryRun (Encodable.encode c) fuel (some []) (decodedLines cert)
    (Encodable.encode (decodedLines cert)) (List.length_le_encode _)
  rw [ht,hz]
  simp only [finishFunction,decodedState,Encodable.encodek,Option.getD_some]
  rw [finishOriginal,Denumerable.ofNat_encode]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HistoryMachine.NativeProof
