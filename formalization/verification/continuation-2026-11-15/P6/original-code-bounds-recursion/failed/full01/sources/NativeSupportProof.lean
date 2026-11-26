module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.NativeSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open NumberedNumericDecoding NumberedSyntaxBoundsPrimrec
open Continuation20261114

def value (n raw : Nat) : Nat :=
  ((decodeCode n raw).map (fun code => Encodable.encode (codeBounds code))).getD 0

def recombination (n raw : Nat) (values : List Nat) : Option Nat :=
  match decodeCode n raw with
  | none => some 0
  | some code => some (Encodable.encode
      (NumberedSyntaxBoundsPrimrecSupportProof.mergeBounds
        (NumberedSyntaxBoundsPrimrecSupportProof.rootBounds code,
         NumberedSyntaxBoundsPrimrecSupportProof.collectBounds (values.map Nat.unpair))))

theorem valueImage (n : Nat) (code : Code (Fin n)) :
    value n (codeNumber code) = Encodable.encode (codeBounds code) := by
  simp only [value,NumberedNumericDecodingProof.codeRoundTrip,Option.map_some,Option.getD_some]

theorem recursiveLaw (n raw param : Nat) :
    recombination n raw ((ArgumentEntriesFrontier.rawChildren raw).map (fun child => value n child)) =
      some (value n raw) := by
  cases hc : decodeCode n raw with
  | none => simp only [recombination,value,hc,Option.map_none,Option.getD_none]
  | some code =>
    have he := NumberedNumericDecodingProof.codeNumericSound n raw code hc
    subst raw
    rw [ArgumentEntriesFrontier.Proof.childrenImage]
    have hm : ((NumberedSyntaxBoundsPrimrecSupportProof.children code).map codeNumber).map
        (fun child => value n child) =
        (NumberedSyntaxBoundsPrimrecSupportProof.children code).map
          (fun child => Encodable.encode (codeBounds child)) := by
      rw [List.map_map]
      apply congrArg (fun f => (NumberedSyntaxBoundsPrimrecSupportProof.children code).map f)
      funext child
      exact valueImage n child
    rw [hm]
    have hv : ((NumberedSyntaxBoundsPrimrecSupportProof.children code).map
        (fun child => Encodable.encode (codeBounds child))).map Nat.unpair =
        (NumberedSyntaxBoundsPrimrecSupportProof.children code).map codeBounds := by
      rw [List.map_map]
      apply congrArg (fun f => (NumberedSyntaxBoundsPrimrecSupportProof.children code).map f)
      funext child
      change Nat.unpair (Encodable.encode (codeBounds child)) = codeBounds child
      rw [OriginalBoundsRecombination.ArithmeticProof.pairEncoding,Nat.unpair_pair]
    simp only [recombination,NumberedNumericDecodingProof.codeRoundTrip,hv,valueImage]
    have h := NumberedSyntaxBoundsPrimrecSupportProof.recombineCalibration code
    have h' := Option.some.inj h
    exact congrArg (fun x : Nat × Nat => some (Encodable.encode x)) h'

theorem layerValue (n raw param : Nat) (values : List Nat) :
    evaluate (layer n) (ofFn ![raw,numbersNumber values,param]) =
      Encodable.encode (recombination n raw values) := by
  rw [layer,InternalAcceptanceCalibrationProof.evalBranch]
  change (if evaluate (OriginalCodeValidityGuard.check n) (ofFn ![raw]) = 0 then 1 else
    evaluate (OriginalBoundsRecombination.recombine n) (ofFn ![raw,numbersNumber values])) = _
  rw [OriginalCodeValidityGuard.NativeProof.nativeValidity,
    OriginalBoundsRecombination.NativeProof.nativeRecombine]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    numbersRoundTrip,Option.getD_some]
  cases hc : decodeCode n raw with
  | none => simp only [recombination,hc]; rfl
  | some code => simp only [recombination,hc]; rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.NativeSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.NativeSupportProof
