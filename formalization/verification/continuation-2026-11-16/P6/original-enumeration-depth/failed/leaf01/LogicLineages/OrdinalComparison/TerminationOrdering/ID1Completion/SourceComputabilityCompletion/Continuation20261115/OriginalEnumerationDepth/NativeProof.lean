module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.NativeSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open Continuation20261114 NativeSupportProof

theorem extractValue (n raw param : Nat) : evaluate (extract n) (ofFn ![raw,param]) = value n raw := by
  exact ExchangeSelectedRecursor.NativeProof.nativeFinalValue rank dependency (layer n)
    (fun raw _ => raw) (fun raw _ => ArgumentEntriesFrontier.rawChildren raw)
    (fun raw values _ => recombination n raw values) (fun raw _ => value n raw)
    (fun _ _ => rfl) ArgumentEntriesFrontier.Proof.dependencyValue
    (fun raw values param => layerValue n raw param values)
    (fun raw _ child hc => ArgumentEntriesFrontier.Proof.rawDecrease raw child hc)
    (fun raw param => recursiveLaw n raw param) raw param

theorem nativeDepth : Targets.NativeDepth := by
  intro n v
  change evaluate (extract n) (ofFn ![v.get 0,0]) = _
  exact extractValue n (v.get 0) 0

theorem typedDepth (n : Nat) (code : NumberedAuxiliaryCoding.Code (Fin n)) :
    evaluate (depth n) (ofFn ![NumberedLeastCodeRepresentative.codeNumber code]) = NumberedAuxiliaryEnumeration.depth code := by
  rw [nativeDepth]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,NumberedNumericDecodingProof.codeRoundTrip,Option.map_some,Option.getD_some]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.NativeProof
