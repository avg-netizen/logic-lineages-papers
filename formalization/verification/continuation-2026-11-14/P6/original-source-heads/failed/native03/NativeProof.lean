module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.RawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open NumberedLeastCodeRepresentative Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open NumberedFiniteUniverse InternalRawListRecursionEvaluationProof InternalAcceptanceCalibrationProof

theorem filterStepValue (n : Nat) (arity : Fin n → Nat) (head : HeadCode (Fin n))
    (rest : Nat) (symbols : List (Fin n)) (types : List Ty) :
    evaluate (filterStep n arity) (headNumber head ::ᵥ rest ::ᵥ numbersNumber (symbols.map Fin.val) ::ᵥ
      numbersNumber (types.map typeNumber) ::ᵥ nil) =
    if HeadInWindow arity symbols types (decodeHead head) then 1 + Nat.pair (headNumber head) rest else rest := by
  have hw : evaluate (.composition (OriginalHeadWindow.window n arity) ![.projection 0,.projection 2,.projection 3])
      (headNumber head ::ᵥ rest ::ᵥ numbersNumber (symbols.map Fin.val) ::ᵥ numbersNumber (types.map typeNumber) ::ᵥ nil) =
      (decide (HeadInWindow arity symbols types (decodeHead head))).toNat :=
    OriginalHeadWindow.NativeProof.nativeWindow n arity symbols types head
  rw [filterStep,evalBranch,hw]
  by_cases h : HeadInWindow arity symbols types (decodeHead head)
  · simp only [h,decide_true,Bool.toNat_true,Nat.one_ne_zero,ite_false,ite_true,consOfEvaluation]
    rfl
  · simp only [h,decide_false,Bool.toNat_false,ite_true,ite_false]
    rfl

theorem filterFold (n : Nat) (arity : Fin n → Nat) (heads : List (HeadCode (Fin n)))
    (symbols : List (Fin n)) (types : List Ty) :
    (heads.map headNumber).foldr (fun head rest => evaluate (filterStep n arity)
      (head ::ᵥ rest ::ᵥ numbersNumber (symbols.map Fin.val) ::ᵥ numbersNumber (types.map typeNumber) ::ᵥ nil)) 0 =
    numbersNumber ((heads.filter (fun head => decide (HeadInWindow arity symbols types (decodeHead head)))).map headNumber) := by
  induction heads with
  | nil => rfl
  | cons head heads ih =>
    rw [List.map_cons,List.foldr_cons,filterStepValue,ih]
    by_cases h : HeadInWindow arity symbols types (decodeHead head) <;>
      simp [h,List.filter_cons,numbersNumber]

theorem filterValue (n : Nat) (arity : Fin n → Nat) (heads : List (HeadCode (Fin n)))
    (symbols : List (Fin n)) (types : List Ty) :
    evaluate (filterHeads n arity) (ofFn ![numbersNumber (heads.map headNumber),
      numbersNumber (symbols.map Fin.val),numbersNumber (types.map typeNumber)]) =
    numbersNumber ((heads.filter (fun head => decide (HeadInWindow arity symbols types (decodeHead head)))).map headNumber) := by
  have h := actualRawListRecursionEvaluation 2 (constant 2 0) (filterStep n arity)
    (numbersNumber (symbols.map Fin.val) ::ᵥ numbersNumber (types.map typeNumber) ::ᵥ nil) (numbersNumber (heads.map headNumber))
  change evaluate (filterHeads n arity) (ofFn ![numbersNumber (heads.map headNumber),
    numbersNumber (symbols.map Fin.val),numbersNumber (types.map typeNumber)]) = _ at h
  rw [h,numbersRoundTrip]
  exact filterFold n arity heads symbols types

theorem sourceValue (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (types : List Ty) :
    evaluate (sourceHeads n arity) (ofFn ![numbersNumber (symbols.map Fin.val),numbersNumber (types.map typeNumber)]) =
      numbersNumber ((NumberedAuxiliaryEnumeration.sourceHeads arity symbols types).map headNumber) := by
  rw [sourceHeads,ternaryCompositionEvaluation,RawProof.nativeRawWindow]
  have hm : (rawHeadWindow symbols types).map (fun head => headNumber (headCode head)) =
      ((rawHeadWindow symbols types).map headCode).map headNumber := by rw [List.map_map]; rfl
  rw [hm]
  have hf := filterValue n arity ((rawHeadWindow symbols types).map headCode) symbols types
  have h0 : evaluate (.projection (0 : Fin 2))
      (ofFn ![numbersNumber (symbols.map Fin.val),numbersNumber (types.map typeNumber)]) =
      numbersNumber (symbols.map Fin.val) := rfl
  have h1 : evaluate (.projection (1 : Fin 2))
      (ofFn ![numbersNumber (symbols.map Fin.val),numbersNumber (types.map typeNumber)]) =
      numbersNumber (types.map typeNumber) := rfl
  rw [h0,h1,hf]
  congr 1
  simp [NumberedAuxiliaryEnumeration.sourceHeads,headWindow,List.filter_map,
    NumberedAuxiliaryDecodingProof.headRoundTrip]

theorem nativeSourceHeads : Targets.NativeSourceHeads := by
  intro n arity symbols types
  constructor
  · exact sourceValue n arity symbols types
  · intro head
    rw [member,binaryCompositionEvaluation]
    have hs : evaluate (.composition (sourceHeads n arity) ![.projection 1,.projection 2])
        (ofFn ![headNumber head,numbersNumber (symbols.map Fin.val),numbersNumber (types.map typeNumber)]) =
        numbersNumber ((NumberedAuxiliaryEnumeration.sourceHeads arity symbols types).map headNumber) :=
      sourceValue n arity symbols types
    rw [hs]
    change evaluate TwoSol20261113.CalibratedPrimary.Membership.contains
      (ofFn ![numbersNumber ((NumberedAuxiliaryEnumeration.sourceHeads arity symbols types).map headNumber),headNumber head]) = _
    rw [OriginalHeadWindow.NativeProof.containsValue]
    have hm : headNumber head ∈ (NumberedAuxiliaryEnumeration.sourceHeads arity symbols types).map headNumber ↔
        head ∈ NumberedAuxiliaryEnumeration.sourceHeads arity symbols types := by
      constructor
      · intro h
        obtain ⟨other,ho,he⟩ := List.mem_map.mp h
        exact NumberedLeastCodeRepresentativeSupportProof.headNumberInjective he ▸ ho
      · exact List.mem_map_of_mem
    simp only [hm]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.NativeProof
