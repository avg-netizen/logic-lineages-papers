module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.CodecSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.NativeProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedHeadCodecPrimrec
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open CodecSupportProof

def boolNumber (b : Bool) : Nat := if b then Nat.pair 1 0 else 0
def applicationNumber (p : Ty × Ty) : Nat := Nat.pair 4 (Nat.pair (typeNumber p.1) (typeNumber p.2))
def rankNumber {n : Nat} (i : Fin n) : Nat := Nat.pair 5 i.val
def dataNumber (n : Nat) : HeadData n → Nat :=
  Sum.elim boolNumber (Sum.elim (fun t => Nat.pair 2 (typeNumber t))
    (Sum.elim (fun t => Nat.pair 3 (typeNumber t)) (Sum.elim applicationNumber rankNumber)))

theorem dataCalibration (n raw : Nat) : evaluate (convert n) (ofFn ![raw]) = decoded (dataNumber n) raw := by
  unfold convert dataNumber
  apply sumCalibration
  · exact booleanCalibration
  · intro x
    apply sumCalibration
    · exact typeCalibration 2
    · intro y
      apply sumCalibration
      · exact typeCalibration 3
      · intro z
        apply sumCalibration
        · exact productCalibration
        · exact rankedCalibration n

theorem dataNumberOriginal (n : Nat) :
    (fun d : HeadData n => headNumber ((headEquiv n).symm d)) = dataNumber n := by
  funext d
  rcases d with b | t | t | ⟨s,t⟩ | i
  · cases b <;> rfl
  all_goals rfl

theorem nativeConversion : Targets.NativeConversion := by
  intro n raw
  have hd : (Encodable.decode raw : Option (HeadCode (Fin n))) =
      (Encodable.decode raw : Option (HeadData n)).map (headEquiv n).symm := by
    with_reducible_and_instances change @Encodable.decode _ (Encodable.ofEquiv (HeadData n) (headEquiv n)) raw = _
    exact Encodable.decode_ofEquiv (headEquiv n) raw
  rw [hd,Option.map_map]
  change evaluate (convert n) (ofFn ![raw]) = decoded
    (fun d : HeadData n => headNumber ((headEquiv n).symm d)) raw
  rw [dataNumberOriginal]
  exact dataCalibration n raw

theorem encodedHead (n : Nat) (h : HeadCode (Fin n)) :
    evaluate (convert n) (ofFn ![Encodable.encode h]) = headNumber h := by
  rw [nativeConversion,Encodable.encodek]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.NativeProof
