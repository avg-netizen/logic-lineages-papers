module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.NativeLawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.OriginalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedAuxiliaryCoding

theorem numericLayerAt (n : Nat) (ts : List Source.Ty) (hs : List (HeadCode (Fin n)))
    (ls tb vb : Nat) (prior opened : List (Code (Fin n))) :
    numericLayer n vb (Encodable.encode (ts,hs,ls,tb)) (Encodable.encode prior) (Encodable.encode opened) =
      Encodable.encode (NumberedCodeEnumerationPrimrecSupportProof.layer n ((ts,hs,ls,tb),vb,prior,opened)) := by
  have hxs : (List.Vector.ofFn ![
      (Nat.unpair (Encodable.encode (ts,hs,ls,tb))).1,
      (Nat.unpair (Nat.unpair (Encodable.encode (ts,hs,ls,tb))).2).1,
      (Nat.unpair (Nat.unpair (Nat.unpair (Encodable.encode (ts,hs,ls,tb))).2).2).1,
      (Nat.unpair (Nat.unpair (Nat.unpair (Encodable.encode (ts,hs,ls,tb))).2).2).2,
      vb,Encodable.encode prior,Encodable.encode opened]) =
      List.Vector.ofFn ![Encodable.encode ts,Encodable.encode hs,ls,tb,vb,Encodable.encode prior,Encodable.encode opened] := by
    simp only [Encodable.encode_prod_val,Encodable.encode_nat,Nat.unpair_pair]
  unfold numericLayer
  rw [hxs]
  exact OriginalEnumerationConstructorLayer.NativeProof.nativeLayer n ts hs ls tb vb prior opened

theorem numericOriginal (n : Nat) (data : NumberedCodeEnumerationPrimrecSupportProof.Parameters n)
    (variableBound fuel : Nat) :
    numeric n fuel variableBound (Encodable.encode data) =
      Encodable.encode (NumberedAuxiliaryEnumeration.enumerate data.1 data.2.1 data.2.2.1 data.2.2.2 variableBound fuel) := by
  rcases data with ⟨ts,hs,ls,tb⟩
  induction fuel generalizing variableBound with
  | zero => rfl
  | succ fuel ih =>
    rw [numeric,ih variableBound,ih (variableBound+1),numericLayerAt]
    exact congrArg Encodable.encode (NumberedCodeEnumerationPrimrecSupportProof.layerCalibration n (ts,hs,ls,tb) variableBound fuel)

theorem nativeOriginal : Targets.NativeOriginal := by
  intro n data variableBound fuel
  rw [NativeLawProof.nativeNumeric]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    Encodable.encode_prod_val,Encodable.encode_nat,Nat.unpair_pair]
  exact numericOriginal n data variableBound fuel
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.OriginalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.OriginalProof
