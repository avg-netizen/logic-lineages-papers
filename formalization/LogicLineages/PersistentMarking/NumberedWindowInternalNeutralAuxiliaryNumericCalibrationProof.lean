module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryNumericRecognitionProof
import LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsScalarProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementNumericRecognitionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementNumericCalibrationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxFreeRefinementNumericTerminalProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryNumericCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalNeutralAuxiliaryRefinement
open NumberedWindowInternalNeutralAuxiliaryNumericRecognitionProof
open NumberedWindowInternalAuxBottomRefinement (sourceFlag)
open NumberedWindowInternalAuxBottomRefinementNumericTargets (packedAuxBottom)
open NumberedWindowInternalAuxBottomRefinementNumericRecognitionProof (exactRecognizer)
open NumberedWindowInternalAuxBottomRefinementNumericCalibrationProof (exactPreserved)
open NumberedWindowInternalAuxFreeRefinementNumericTerminalProof (exact_ConcreteAuxFreeAddressPositive)
open NumberedWindowInternalAtomicRefinement (bottomTarget)
open NumberedWindowInternalAtomicRefinementNumericFieldsProof
  (literalFields exactBottomTarget sourceValue targetValue)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (branchEvaluation bothEvaluation compositeTwo compareEvaluation)
open NumberedWindowInternalFreshProbeDispatchProgram (compareNumbers)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult rawLeast)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowAtomicRawStep (freeRaw bottomRaw)
open NumberedWindowConcretePositiveEndpointsScalarProof (scalarEndpoints)
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowAtomicPositiveTargets (packedAddress bottomAddress)
open NumberedWindowScalarAlgorithm (Settings scalar)
open NumberedWindowConcreteCheckers (positive)
open NumberedWindowCopyAlgorithm (Entries)

private theorem sameFieldValue (p : Program 1) (x w y : Nat) :
    evaluate (sameField p) (x ::ᵥ w ::ᵥ y ::ᵥ nil) =
      if run p x = run p y then 1 else 0 := by
  change evaluate (.composition compareNumbers
    (Fin.cons (NumberedWindowInternalAtomicRefinement.atSource p)
      (Fin.cons (NumberedWindowInternalAtomicRefinement.atTarget p) Fin.elim0)))
    (x ::ᵥ w ::ᵥ y ::ᵥ nil) = _
  rw [compositeTwo,sourceValue,targetValue,compareEvaluation]

theorem exact_MatchingBottomAuxTarget (c dom cod stored name inputArg w outputArg : Nat) :
    evaluate bottomAuxTarget (packedAuxFree c dom cod stored name inputArg ::ᵥ w ::ᵥ
      packedAuxBottom c dom cod stored outputArg ::ᵥ nil) = 1 := by
  let x := packedAuxFree c dom cod stored name inputArg
  let y := packedAuxBottom c dom cod stored outputArg
  have hx := literalFields c cod
    (NumberedWindowAtomicApplicationTargets.auxRaw dom cod (freeRaw stored name) inputArg)
  have hy := literalFields c cod
    (NumberedWindowAtomicApplicationTargets.auxRaw dom cod (bottomRaw stored) outputArg)
  have parsed : run sourceFlag y = 1 :=
    ((exactRecognizer y).1).mpr ⟨c,dom,cod,stored,outputArg,rfl⟩
  have xc : run rawContext x = c := by simpa only [x,packedAuxFree] using hx.1
  have yc : run rawContext y = c := by simpa only [y,packedAuxBottom] using hy.1
  have xr : run rawResult x = cod := by simpa only [x,packedAuxFree] using hx.2.1
  have yr : run rawResult y = cod := by simpa only [y,packedAuxBottom] using hy.2.1
  have xd : run auxDom x = dom := (auxCoordinates c dom cod _ inputArg).1
  have yd : run auxDom y = dom := (auxCoordinates c dom cod _ outputArg).1
  have xf : run auxFnType x = stored := freeStored c dom cod stored name inputArg
  have yf : run auxFnType y = stored := bottomStored c dom cod stored outputArg
  change evaluate bottomAuxTarget (x ::ᵥ w ::ᵥ y ::ᵥ nil) = 1
  simp only [bottomAuxTarget,bothEvaluation,targetValue,sameFieldValue,
    parsed,xc,yc,xr,yr,xd,yd,xf,yf,if_pos,and_self,eq_self,true_and, and_true]

private theorem freeCandidate (xs : Entries) (s : Settings) (i : Program 1)
    (scalarCal : ∀ y, run i y = (scalar s y).toNat)
    (c dom cod stored name arg w y : Nat)
    (accepted : positive xs s (packedAuxFree c dom cod stored name arg) w y = true) :
    evaluate (freeAuxTarget i) (packedAuxFree c dom cod stored name arg ::ᵥ w ::ᵥ y ::ᵥ nil) = 1 := by
  have endpoint := exact_ConcreteAuxFreeAddressPositive xs s c dom cod stored name arg w y (by simpa only [packedAuxFree] using accepted)
  have v := exactBottomTarget.2 c cod
    (NumberedWindowAtomicApplicationTargets.auxRaw dom cod (freeRaw stored name) arg) w y
  have bottom :
      evaluate bottomTarget (packedAuxFree c dom cod stored name arg ::ᵥ w ::ᵥ y ::ᵥ nil) =
      if y = bottomAddress c cod then 1 else 0 := by simpa only [packedAuxFree] using v
  rw [freeAuxTarget,branchEvaluation,bottom]
  by_cases equal : y = bottomAddress c cod
  · have hscalar : scalar s y = true := (scalarEndpoints xs s _ w y accepted).2
    have terminal :
        evaluate bottomTarget (packedAuxFree c dom cod stored name arg ::ᵥ w ::ᵥ y ::ᵥ nil) = 1 :=
      bottom.trans (if_pos equal)
    have carrier : run i y = 1 := by rw [scalarCal,hscalar]; rfl
    rw [if_pos equal,if_neg Nat.one_ne_zero,bothEvaluation,terminal,targetValue,carrier] <;> simp
  · rcases endpoint with ⟨h,_⟩ | ⟨_,_,out,_,shape,_,_⟩
    · exact False.elim (equal h)
    · simp only [if_neg equal,if_pos rfl]
      rw [show y = packedAuxBottom c dom cod stored out from shape]
      exact exact_MatchingBottomAuxTarget c dom cod stored name arg w out

/-- Original concrete all-raw calibration. Both branches retain the original
witness and original r; the bottom-auxiliary branch does not invoke i. -/
theorem exact_OriginalNeutralPositive (xs : Entries) (s : Settings) (i : Program 1) (r : Program 3)
    (scalarCal : ∀ y, run i y = (scalar s y).toNat)
    (old : ∀ x w y, evaluate r (x ::ᵥ w ::ᵥ y ::ᵥ nil) = (positive xs s x w y).toNat) :
    ∀ x w y, evaluate (neutralPositive i r) (x ::ᵥ w ::ᵥ y ::ᵥ nil) =
      (positive xs s x w y).toNat := by
  intro x w y
  rw [neutralPositive,branchEvaluation,sourceValue]
  rcases freeBit x with miss | hit
  · rw [if_pos miss]
    exact exactPreserved xs s i r scalarCal old x w y
  · rw [hit,if_neg Nat.one_ne_zero,bothEvaluation,old]
    cases ok : positive xs s x w y with
    | false => simp
    | true =>
      obtain ⟨c,dom,cod,stored,name,arg,rfl⟩ := (freeRecognition x).mp hit
      have test := freeCandidate xs s i scalarCal c dom cod stored name arg w y ok
      simp [test]

#print axioms exact_MatchingBottomAuxTarget
#print axioms exact_OriginalNeutralPositive
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryNumericCalibrationProof
