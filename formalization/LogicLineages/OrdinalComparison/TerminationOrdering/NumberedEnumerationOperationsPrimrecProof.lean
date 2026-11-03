module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedEnumerationOperationsPrimrecTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedEnumerationOperationsPrimrecProof
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open NumberedAuxiliaryEnumeration NumberedFiniteUniverse NumberedHeadCodecPrimrecSupportProof

def typeListStep (p : List Ty × List (List Ty)) : List (List Ty) :=
  [] :: p.1.flatMap (fun tau => p.2.map (List.cons tau))

theorem typeListStepPrimitive : Primrec typeListStep :=
  Primrec.list_cons.comp (Primrec.const [])
    (Primrec.list_flatMap Primrec.fst
      (Primrec.list_map (Primrec.snd.comp Primrec.fst)
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂)

theorem typeListsPrimitive : NumberedEnumerationOperationsPrimrecTargets.ActualTypeListsPrimitive := by
  change Primrec₂ typeLists
  have hstep : Primrec₂ (fun S (p : Nat × List (List Ty)) => typeListStep (S, p.2)) :=
    (typeListStepPrimitive.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))).to₂
  apply (Primrec.nat_rec (Primrec.const ([[]] : List (List Ty))) hstep).of_eq
  intro S bound
  induction bound with
  | zero => rfl
  | succ bound ih => exact congrArg (fun previous => typeListStep (S, previous)) ih

def rawHeadCodes (n : Nat) (p : List (Fin n) × List Ty) : List (HeadCode (Fin n)) :=
  [.zero, .succ] ++ p.2.flatMap (fun tau => [.cases tau, .recursor tau]) ++
    p.2.flatMap (fun sigma => p.2.map (fun tau => .application sigma tau)) ++
      p.1.map .ranked

theorem rawHeadCodesPrimitive (n : Nat) : Primrec (rawHeadCodes n) := by
  have hcases : Primrec (fun p : List (Fin n) × List Ty =>
      p.2.flatMap (fun tau => ([HeadCode.cases tau, HeadCode.recursor tau] : List (HeadCode (Fin n))))) :=
    Primrec.list_flatMap Primrec.snd
      (Primrec.list_cons.comp ((casesPrimitive n).comp Primrec.snd)
        (Primrec.list_cons.comp ((recursorPrimitive n).comp Primrec.snd)
          (Primrec.const []))).to₂
  have happ : Primrec (fun p : List (Fin n) × List Ty =>
      p.2.flatMap (fun sigma => p.2.map (fun tau => (HeadCode.application sigma tau : HeadCode (Fin n))))) :=
    Primrec.list_flatMap Primrec.snd
      (Primrec.list_map (Primrec.snd.comp Primrec.fst)
        ((applicationPrimitive n).comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂).to₂
  have hranked : Primrec (fun p : List (Fin n) × List Ty =>
      p.1.map (HeadCode.ranked : Fin n → HeadCode (Fin n))) :=
    Primrec.list_map Primrec.fst ((rankedPrimitive n).comp Primrec.snd).to₂
  exact Primrec.list_append.comp
    (Primrec.list_append.comp
      (Primrec.list_append.comp (Primrec.const [HeadCode.zero, HeadCode.succ]) hcases) happ) hranked

theorem rawHeadCodesCalibration (n : Nat) (p : List (Fin n) × List Ty) :
    rawHeadCodes n p = (rawHeadWindow p.1 p.2).map headCode := by
  simp [rawHeadCodes, rawHeadWindow, List.map_flatMap, List.map_map, headCode, Function.comp_def]

theorem sourceHeadsPrimitive : NumberedEnumerationOperationsPrimrecTargets.ActualSourceHeadsPrimitive := by
  intro n arity
  have hdecision : Primrec (fun p : HeadCode (Fin n) × (List (Fin n) × List Ty) =>
      decide (HeadInWindow arity p.2.1 p.2.2 (decodeHead p.1))) :=
    (NumberedHeadWindowPrimrecProof.headWindowPrimitive n arity).comp
      ((Primrec.fst.comp Primrec.snd).pair
        ((Primrec.snd.comp Primrec.snd).pair Primrec.fst))
  have hrelation : PrimrecRel (fun (head : HeadCode (Fin n)) (p : List (Fin n) × List Ty) =>
      HeadInWindow arity p.1 p.2 (decodeHead head)) := hdecision.primrecPred
  apply (hrelation.listFilter.comp (rawHeadCodesPrimitive n) Primrec.id).of_eq
  intro p
  rw [rawHeadCodesCalibration]
  simp [sourceHeads, headWindow, List.filter_map,
    NumberedAuxiliaryDecodingProof.headRoundTrip, Function.comp_def]

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedEnumerationOperationsPrimrecProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedEnumerationOperationsPrimrecProof
