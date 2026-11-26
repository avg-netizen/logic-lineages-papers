module

public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverTargets
import LogicLineages.PersistentMarking.NumberedWindowCoverBoundsProgramProof
import LogicLineages.PersistentMarking.NumberedWindowCoverProgramProof
import LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverNumericProof
open LogicLineages.ComputabilityKnowledge LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptanceCalibrationProof (evalBranch)
open NumberedWindowCoverBoundsAlgorithm (Measure bounds cover)
open NumberedWindowCoverAlgorithm (grammar)
open NumberedWindowCoverBoundsProgramProof (metrics)
open NumberedWindowCoverProgramProof (grammarPrim)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowSyntaxProgramProof (termProgram)
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorOne compositeThree)
open NumberedWindowRawExchangeVerticesChecks (exact_OriginalGuardedExchangeBounds)
open NumberedWindowInternalFactoredCoverTargets

private theorem rawValue (p : Program 1) (xs : List.Vector Nat 3) :
    evaluate (rawCall p) xs = run p (xs.get 2) := by
  change evaluate p (List.Vector.ofFn fun _ : Fin 1 => xs.get 2) = _
  rw [vectorOne] <;> rfl

private theorem generatorValue (M : Program 1) (G : Program 3) (H K : List Nat) (n : Nat)
    (measure : TermMeasureCalibrated M) (grammarCall : GrammarOptionCalibrated G) :
    let tape := Encodable.encode H ::ᵥ Encodable.encode K ::ᵥ n ::ᵥ nil
    evaluate (generatorCall M G) tape =
      Encodable.encode (some (grammar H K (bounds n).1.2 (bounds n).1.1).1) := by
  dsimp only
  rw [generatorCall,compositeThree,rawValue]
  change evaluate G
    (Encodable.encode H ::ᵥ Encodable.encode K ::ᵥ evaluate M (n ::ᵥ nil) ::ᵥ nil) = _
  rw [measure n]
  exact grammarCall H K (bounds n).1

theorem calibration : ExactFactoredCoverCalibration := by
  intro V M G syntaxCal measure grammarCall H K n
  rw [factoredCover,evalBranch,rawValue]
  change (if run V n = 0 then 0 else
    evaluate (generatorCall M G) (Encodable.encode H ::ᵥ Encodable.encode K ::ᵥ n ::ᵥ nil)) =
      Encodable.encode (cover H K n)
  rw [syntaxCal n,generatorValue M G H K n measure grammarCall]
  cases valid : (syntaxBits n).1 <;> simp [cover,valid]

private theorem measureExists : ∃ M : Program 1, TermMeasureCalibrated M :=
  (GorbowPRProgram.Proof.unaryCorrespondence _).mp (Primrec.encode.comp (Primrec.fst.comp metrics))

private theorem grammarExists : ∃ G : Program 3, GrammarOptionCalibrated G := by
  let Input := List.Vector Nat 3
  let readList (n : Nat) := ((Encodable.decode n : Option (List Nat)).getD [])
  let readBounds (n : Nat) := ((Encodable.decode n : Option Measure).getD (0,0))
  have readListPrim : Primrec readList := Primrec.option_getD.comp Primrec.decode (Primrec.const [])
  have readBoundsPrim : Primrec readBounds := Primrec.option_getD.comp Primrec.decode (Primrec.const (0,0))
  have second : Primrec (fun v : Input => v.tail.head) := Primrec.vector_head.comp Primrec.vector_tail
  have third : Primrec (fun v : Input => v.tail.tail.head) :=
    Primrec.vector_head.comp (Primrec.vector_tail.comp Primrec.vector_tail)
  have H : Primrec (fun v : Input => readList v.head) := readListPrim.comp Primrec.vector_head
  have K := readListPrim.comp second
  have m := readBoundsPrim.comp third
  have compute := grammarPrim.comp (H.pair (K.pair (Primrec.snd.comp m))) (Primrec.fst.comp m)
  have result : Primrec (fun v : Input => (some
      (grammar (readList v.head) (readList v.tail.head) (readBounds v.tail.tail.head).2
        (readBounds v.tail.tail.head).1).1 : Option (List Nat))) :=
    Primrec.option_some.comp (Primrec.fst.comp compute)
  obtain ⟨G,agrees⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 _ (Primrec.encode.comp result)
  exact ⟨G,fun H K m => by simpa [readList,readBounds] using
    agrees (Encodable.encode H ::ᵥ Encodable.encode K ::ᵥ Encodable.encode m ::ᵥ nil)⟩

theorem selected : ExactSelectedFactoredCover := by
  obtain ⟨V,syntaxCal⟩ := termProgram
  obtain ⟨M,measure⟩ := measureExists
  obtain ⟨G,grammarCall⟩ := grammarExists
  exact ⟨V,M,G,syntaxCal,measure,grammarCall,calibration V M G syntaxCal measure grammarCall⟩

theorem invariance : ExactMeasureExchangeInvariance := by
  intro M measure hp a b move
  rw [measure a,measure b,(exact_OriginalGuardedExchangeBounds hp a b).1 move]

end LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverNumericProof
