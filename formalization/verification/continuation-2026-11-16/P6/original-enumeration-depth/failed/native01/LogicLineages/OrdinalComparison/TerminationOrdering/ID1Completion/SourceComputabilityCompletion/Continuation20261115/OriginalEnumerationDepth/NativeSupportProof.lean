module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.ArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.NativeSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open NumberedNumericDecoding
open Continuation20261114
def value (n raw : Nat) : Nat := ((decodeCode n raw).map NumberedAuxiliaryEnumeration.depth).getD 0

def recombination (n raw : Nat) (values : List Nat) : Option Nat :=
  match decodeCode n raw with
  | none => some 0
  | some _ => some (1 + values.foldr max 0)

theorem valueImage (n : Nat) (code : Code (Fin n)) :
    value n (codeNumber code) = NumberedAuxiliaryEnumeration.depth code := by
  simp only [value,NumberedNumericDecodingProof.codeRoundTrip,Option.map_some,Option.getD_some]

theorem sourceRecurrence {n : Nat} (code : Code (Fin n)) :
    1 + ((NumberedSyntaxBoundsPrimrecSupportProof.children code).map NumberedAuxiliaryEnumeration.depth).foldr max 0 =
      NumberedAuxiliaryEnumeration.depth code := by
  cases code <;> simp [NumberedSyntaxBoundsPrimrecSupportProof.children,
    NumberedAuxiliaryEnumeration.depth,Nat.max_zero_right]

theorem foldValue (xs : List Nat) :
    xs.foldr (fun head acc => evaluate OriginalBoundsRecombination.maximum (head ::ᵥ acc ::ᵥ nil)) 0 = xs.foldr max 0 := by
  induction xs with
  | nil => rfl
  | cons head tail ih => rw [List.foldr_cons,ih,OriginalBoundsRecombination.ArithmeticProof.maximumValue,List.foldr_cons]

theorem collectValue (raw : Nat) : evaluate collect (raw ::ᵥ nil) =
    ((decodeNumbers raw).getD []).foldr max 0 := by
  rw [collect,InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation]
  change ((decodeNumbers raw).getD []).foldr (fun head acc => evaluate OriginalBoundsRecombination.maximum (head ::ᵥ acc ::ᵥ nil)) 0 = _
  exact foldValue _

theorem recursiveLaw (n raw param : Nat) :
    recombination n raw ((ArgumentEntriesFrontier.rawChildren raw).map (fun child => value n child)) = some (value n raw) := by
  cases hc : decodeCode n raw with
  | none => simp only [recombination,value,hc,Option.map_none,Option.getD_none]
  | some code =>
    have he := NumberedNumericDecodingProof.codeNumericSound n raw code hc
    subst raw
    rw [ArgumentEntriesFrontier.Proof.childrenImage]
    have hm : ((NumberedSyntaxBoundsPrimrecSupportProof.children code).map codeNumber).map (fun child => value n child) =
        (NumberedSyntaxBoundsPrimrecSupportProof.children code).map NumberedAuxiliaryEnumeration.depth := by
      rw [List.map_map]
      apply congrArg (fun f => (NumberedSyntaxBoundsPrimrecSupportProof.children code).map f)
      funext child
      exact valueImage n child
    simp only [recombination,NumberedNumericDecodingProof.codeRoundTrip,hm,valueImage,sourceRecurrence]

theorem layerValue (n raw param : Nat) (values : List Nat) :
    evaluate (layer n) (ofFn ![raw,numbersNumber values,param]) = Encodable.encode (recombination n raw values) := by
  rw [layer,InternalAcceptanceCalibrationProof.evalBranch]
  change (if evaluate (OriginalCodeValidityGuard.check n) (ofFn ![raw]) = 0 then 1 else
    (evaluate collect (ofFn ![numbersNumber values]) + 1) + 1) = _
  rw [OriginalCodeValidityGuard.NativeProof.nativeValidity,InternalEqualityTestEvaluationProof.vectorOne,collectValue]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,numbersRoundTrip,Option.getD_some]
  cases hc : decodeCode n raw with
  | none => simp only [recombination,hc]; rfl
  | some code =>
    simp only [recombination,hc,Option.isSome_some,Bool.toNat_true,Nat.one_ne_zero,ite_false,Encodable.encode_some]
    omega
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.NativeSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.NativeSupportProof
