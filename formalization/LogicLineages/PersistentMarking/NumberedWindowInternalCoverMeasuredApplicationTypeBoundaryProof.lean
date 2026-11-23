module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationTypeBoundaryTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationTypeBoundaryProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open ID1Completion.InternalEqualityTestEvaluationProof (vectorTwo)
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open NumberedWindowAddressAlgorithm (nextType typeTable typeBit)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowAnnotationAlgorithm (arrow)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseFieldParserRawPairProof (encodedPair tailBound)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipNumericChecks (exact_AllInputScratchMembership)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (grammarTypeAt refitGuard)
open NumberedWindowInternalCoverMeasuredApplicationTypeCalibrationTargets (refittedScalarType)
open NumberedWindowInternalCoverMeasuredApplicationTypeBoundaryTargets

private theorem tableLength (n : Nat) : (typeTable n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [typeTable,ih]

private theorem earlier {n i : Nat} (bound : i < n) :
    (typeTable n)[i]? = some (typeBit i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases prior : i < n
    · simp only [typeTable,List.getElem?_append_left (tableLength n ▸ prior)]
      exact ih prior
    · have last : i = n := by omega
      subst i
      change (typeTable n ++ [typeBit n])[n]? = some (typeBit n)
      simpa only [tableLength] using
        (List.getElem?_concat_length (l := typeTable n) (a := typeBit n))

private theorem previous {n i : Nat} (bound : i < n) :
    (typeTable n).getD i false = typeBit i := by
  rw [List.getD_eq_getElem?_getD,earlier bound]
  rfl

theorem exact_TypeBitArrowLaw : ExactTypeBitArrowLaw := by
  intro dom cod
  have domainBound : dom < pair dom cod + 1 := by
    have le : dom ≤ pair dom cod := by
      unfold pair
      omega
    omega
  have codomainBound : cod < pair dom cod + 1 :=
    Nat.lt_succ_of_le (tailBound dom cod)
  change nextType (pair dom cod + 1) (typeTable (pair dom cod + 1)) = _
  rw [nextType,encodedPair,previous domainBound,previous codomainBound]

theorem exact_ValidArrowCodeChain : ExactValidArrowCodeChain := by
  intro depth
  induction depth with
  | zero => exact ⟨Nat.le_refl 0,rfl⟩
  | succ depth ih =>
    constructor
    · change depth + 1 ≤ arrow 0 (arrowCodeChain depth)
      have above : arrowCodeChain depth < arrow 0 (arrowCodeChain depth) :=
        Nat.lt_succ_of_le (tailBound 0 (arrowCodeChain depth))
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih.1 above)
    · change typeBit (arrow 0 (arrowCodeChain depth)) = true
      rw [exact_TypeBitArrowLaw]
      have ground : typeBit 0 = true := rfl
      rw [ground,ih.2]
      rfl

theorem exact_ValidTypeCodesUnbounded : ExactValidTypeCodesUnbounded := by
  intro bound
  have chain := exact_ValidArrowCodeChain (bound + 1)
  exact ⟨arrowCodeChain (bound + 1),
    Nat.lt_of_lt_of_le (Nat.lt_succ_self bound) chain.1,chain.2⟩

private def finiteBound : List Nat → Nat
  | [] => 0
  | head :: tail => max head (finiteBound tail)

private theorem memberBound (codes : List Nat) {code : Nat} (member : code ∈ codes) :
    code ≤ finiteBound codes := by
  induction codes with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | present
    · subst code
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih present) (Nat.le_max_right _ _)

theorem exact_FiniteTypeListOmission : ExactFiniteTypeListOmission := by
  intro codes
  obtain ⟨code,large,valid⟩ := exact_ValidTypeCodesUnbounded (finiteBound codes)
  refine ⟨code,valid,eq_false_of_ne_true ?_⟩
  intro present
  have small := memberBound codes (List.contains_iff_mem.mp present)
  exact (Nat.not_lt_of_ge small) large

theorem exact_NoAllTypesWindowed : ExactNoAllTypesWindowed := by
  intro s all
  obtain ⟨code,valid,missing⟩ := exact_FiniteTypeListOmission s.window.1
  have present := all code valid
  rw [missing] at present
  cases present

private theorem listCode (codes : List Nat) : Encodable.encode codes = numbersNumber codes := by
  induction codes with
  | nil => rfl
  | cons code codes ih =>
    rw [Encodable.encode_list_cons,Encodable.encode_nat,ih,numbersNumber,Nat.add_comm 1] <;> rfl

private theorem grammarAbsent (s : Settings) (code : Nat)
    (missing : s.types.contains code = false) :
    evaluate (grammarTypeAt s) (code ::ᵥ nil) = 0 := by
  let types := s.types
  let tape := code ::ᵥ nil
  let calls : Fin 2 → Program 1 :=
    ![NumberedWindowInternalFreshProbeDispatchProgram.literal 1 (Encodable.encode types),.projection 0]
  change evaluate scratchMember (List.Vector.ofFn (fun i => evaluate (calls i) tape)) = 0
  rw [vectorTwo]
  change evaluate scratchMember
    (evaluate (NumberedWindowInternalFreshProbeDispatchProgram.literal 1 (Encodable.encode types)) tape
      ::ᵥ code ::ᵥ nil) = 0
  rw [literalEvaluation,exact_AllInputScratchMembership,listCode,numbersRoundTrip]
  have noHit : (types.any (fun head => head == code)) ≠ true := by
    intro hit
    obtain ⟨head,present,same⟩ := List.any_eq_true.mp hit
    have equality : head = code := eq_of_beq same
    subst head
    have listed : s.types.contains code = true := List.contains_iff_mem.mpr present
    rw [missing] at listed
    cases listed
  change (types.any (fun head => head == code)).toNat = 0
  rw [eq_false_of_ne_true noHit]
  rfl

theorem exact_RefittedValidTypeRejection : ExactRefittedValidTypeRejection := by
  intro s TV T
  obtain ⟨code,valid,missing⟩ := exact_FiniteTypeListOmission s.types
  have grammar : evaluate (grammarTypeAt s) (code ::ᵥ nil) = 0 :=
    grammarAbsent s code missing
  have refit : evaluate (refitGuard s T) (code ::ᵥ nil) = 0 := by
    rw [refitGuard,actualConjunctionEvaluation,grammar]
    simp
  have refitted : evaluate (refittedScalarType s TV T) (code ::ᵥ nil) = 0 := by
    rw [refittedScalarType,actualConjunctionEvaluation,refit]
    simp
  exact ⟨code,valid,grammar,refit,refitted⟩

theorem exact_ActualTypeRefitCounterexample : ExactActualTypeRefitCounterexample := by
  intro s TV T actual
  obtain ⟨cod,valid,_,rejected,_⟩ := exact_RefittedValidTypeRejection s TV T
  have ground : typeBit 0 = true := rfl
  have arrowValid : typeBit (arrow 0 cod) = true := by
    rw [exact_TypeBitArrowLaw,ground,valid]
    rfl
  exact ⟨cod,(actual (arrow 0 cod)).trans (congrArg Bool.toNat arrowValid),
    (actual 0).trans (congrArg Bool.toNat ground),
    (actual cod).trans (congrArg Bool.toNat valid),rejected⟩

theorem exact_RefittedTypeGuardNeverActual : ExactRefittedTypeGuardNeverActual := by
  intro s TV T actual
  obtain ⟨code,valid,_,_,rejected⟩ := exact_RefittedValidTypeRejection s TV T
  have accepted : evaluate (refittedScalarType s TV T) (code ::ᵥ nil) = 1 :=
    (actual code).trans (congrArg Bool.toNat valid)
  rw [rejected] at accepted
  cases accepted

theorem exact_RefittedInstalledTupleImpossible : ExactRefittedInstalledTupleImpossible := by
  intro xs s W i j cv TV T d p₀ raw least v installed
  obtain ⟨_,_,callbacks,_⟩ := installed
  obtain ⟨_,actual,_⟩ := callbacks
  exact exact_RefittedTypeGuardNeverActual s TV T actual

#print axioms exact_TypeBitArrowLaw
#print axioms exact_ValidArrowCodeChain
#print axioms exact_ValidTypeCodesUnbounded
#print axioms exact_FiniteTypeListOmission
#print axioms exact_NoAllTypesWindowed
#print axioms exact_RefittedValidTypeRejection
#print axioms exact_ActualTypeRefitCounterexample
#print axioms exact_RefittedTypeGuardNeverActual
#print axioms exact_RefittedInstalledTupleImpossible

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationTypeBoundaryProof
