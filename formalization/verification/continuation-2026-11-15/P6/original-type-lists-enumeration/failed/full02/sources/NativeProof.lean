module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.CodecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

theorem encodedValue (types : List Source.Ty) (count : Nat) :
    evaluate enumeration (ofFn ![count,Encodable.encode types]) =
      Encodable.encode (NumberedAuxiliaryEnumeration.typeLists types count) := by
  rw [CodecProof.listEncoding types,NumericProof.enumerationValue,CodecProof.tuplesEncoding]
  exact (CodecProof.listEncoding _).symm

theorem nativeEnumeration : Targets.NativeEnumeration := by
  intro v
  obtain ⟨types,he⟩ := CodecProof.originalTypeListImage (v.get 1)
  have hget : v.get = ![v.get 0,v.get 1] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  have hv := congrArg List.Vector.ofFn hget
  rw [List.Vector.ofFn_get] at hv
  rw [hv]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [← he,Encodable.encodek,Option.getD_some]
  exact encodedValue types (v.get 0)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.NativeProof
