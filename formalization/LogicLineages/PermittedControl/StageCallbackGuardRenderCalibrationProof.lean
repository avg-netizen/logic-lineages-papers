module
public import LogicLineages.PermittedControl.StageCallbackGuardRenderTargets
import LogicLineages.PermittedControl.RawPacketAlgebraJoinCalibrationProof
import LogicLineages.PermittedControl.StableSortedHighFieldStatementChecks
import LogicLineages.PermittedControl.HighFieldComparisonStatementChecks
import LogicLineages.PermittedControl.RawFieldComparisonFormStatementChecks

public section
namespace LogicLineages.PermittedControl.StageCallbackGuardRender
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand LowerOperandCode PreparedPacketCode preparedPacketCode
  preparedTableBytes)
open FieldComparison (ValueField LongFieldCode longFieldCode normalizeShortField sameForm)
open RawPacketAlgebra (encodePacket tableOf appendCode unitCode tableBytes appendCodeEq)
open MixedSameRankResidue (WeightedOperand)
open ActualRawComparisonCeiling (LabelCode PairCode encodeLabel encodePair orderedPairs)
open ActualFullValueLabels (Label labels)
open ActualFullLabelPairGuards (Pair Answer lowerFormula lowerPacket topPacket topRequest)
open ActualFiniteFullValueGuards (pairs compile)
open ActualSignedOrdinaryPairHigh (OrderTest request wantedBit strictPacket equalPacket orientedPacket)
open StableSortedHighField (basePacket orderGuard)

theorem reqTop (a : Answer) : (request (topRequest a).2 (topRequest a).1).1 = a.code := by
  cases a <;> first | rfl | decide | simp [request,topRequest,Answer.code]

theorem wantTop (a : Answer) : wantedBit (topRequest a).2 (topRequest a).1 true = true := by
  cases a <;> first | rfl | decide | simp [wantedBit,request,topRequest]

theorem reqRev (a : Answer) : (request (topRequest a).2 (-(topRequest a).1)).1 = 2 - a.code := by
  cases a <;> first | rfl | decide | simp [request,topRequest,Answer.code]

theorem wantRev (a : Answer) : wantedBit (topRequest a).2 (-(topRequest a).1) true = true := by
  cases a <;> first | rfl | decide | simp [wantedBit,request,topRequest]

theorem strictPacketEq (F G : ValueField) (lo : Nat) (c : Int) (k : OrderTest) (w : Nat)
    (hw : (request k c).1 = w) (hb : wantedBit k c true = true) :
    strictPacket F G lo c k true = ((basePacket F G lo w).1 ++ [.coordinate lo],
      .conjunction (orderGuard ((basePacket F G lo w).1.length+1)) (basePacket F G lo w).2) := by
  subst hw
  unfold strictPacket
  rw [hb]
  rfl

theorem equalPacketEq (F G : ValueField) (c : Int) (k : OrderTest) (w : Nat)
    (hw : (request k c).1 = w) (hb : wantedBit k c true = true) :
    equalPacket F G c k true =
      ([],HighFieldPreparedPacket.constantFormula 0 (sameForm (normalizeShortField F) (normalizeShortField G)) w) := by
  subst hw
  unfold equalPacket
  rw [hb]
  rfl

theorem strictFromBaseEq (lo : Nat) (t : List LowerOperand) (φ : NormalForm.Formula) :
    strictFromBase lo (preparedPacketCode t φ) =
      encodePacket (t ++ [.coordinate lo],.conjunction (orderGuard (t.length+1)) φ) := by
  change (Encodable.encode (tableOf (preparedTableBytes t) ++ [slotCode lo]),
      LinearRows.Code.conjunction (orderGuardCode ((tableOf (preparedTableBytes t)).length + 1)) φ.encode) =
    (preparedTableBytes (t ++ [.coordinate lo]),
      (NormalForm.Formula.conjunction (orderGuard (t.length+1)) φ).encode)
  rw [tableBytes,List.length_map]
  simp only [preparedTableBytes,List.map_append,List.map_cons,List.map_nil]
  try rfl

theorem strictCodeEq (F G : ValueField) (lo hi w : Nat) (h : lo < hi) :
    strictCode (longFieldCode F) (longFieldCode G) lo hi w =
      encodePacket ((basePacket F G lo w).1 ++ [.coordinate lo],
        .conjunction (orderGuard ((basePacket F G lo w).1.length+1)) (basePacket F G lo w).2) := by
  unfold strictCode
  rw [(StatementChecks.fixed_stableSortedHighFieldBasePacket F G lo hi w h).1]
  exact strictFromBaseEq lo _ _

theorem constantCodeEq (answer wanted : Nat) :
    constantCode answer wanted = (HighFieldPreparedPacket.constantFormula 0 answer wanted).encode := by
  by_cases h : answer = wanted
  · simp [constantCode,HighFieldPreparedPacket.constantFormula,FieldComparison.flipHighComparisonAnswer,h,
      NormalForm.Formula.encode]
  · simp [constantCode,HighFieldPreparedPacket.constantFormula,FieldComparison.flipHighComparisonAnswer,h,
      NormalForm.Formula.encode]

theorem equalCodeEq (F G : ValueField) (w : Nat) :
    equalCode (longFieldCode F) (longFieldCode G) w =
      encodePacket ([],HighFieldPreparedPacket.constantFormula 0
        (sameForm (normalizeShortField F) (normalizeShortField G)) w) := by
  have nF := StatementChecks.fixed_highFieldComparisonCalibration.1 F
  have nG := StatementChecks.fixed_highFieldComparisonCalibration.1 G
  have same := (StatementChecks.fixed_rawFieldComparisonFormCalibration.2.2
    (normalizeShortField F) (normalizeShortField G)).2.2
  unfold equalCode
  rw [nF,nG,same,constantCodeEq]
  rfl

theorem topEq (F G : ValueField) (i j : Nat) (a : Answer) :
    topCode (longFieldCode F) (longFieldCode G) i j a.code =
      encodePacket (orientedPacket F G i j (topRequest a).1 (topRequest a).2 true) := by
  unfold topCode orientedPacket
  by_cases hij : i < j
  · rw [if_pos hij,if_pos hij,strictPacketEq F G i _ _ a.code (reqTop a) (wantTop a)]
    exact strictCodeEq F G i j a.code hij
  · rw [if_neg hij,if_neg hij]
    by_cases hji : j < i
    · rw [if_pos hji,if_pos hji,strictPacketEq G F j _ _ (2 - a.code) (reqRev a) (wantRev a)]
      exact strictCodeEq G F j i (2 - a.code) hji
    · rw [if_neg hji,if_neg hji,equalPacketEq F G _ _ a.code (reqTop a) (wantTop a)]
      exact equalCodeEq F G a.code

theorem lowerPairEq (p : Pair) (a : Answer) :
    lowerPairCode (encodePair p) a.code = encodePacket (lowerPacket p a) := by
  cases a <;> rfl

theorem pairCodeEq (top : Nat) (p : Pair) (a : Answer) :
    pairCode top (encodePair p) a.code = encodePacket (ActualFullLabelPairGuards.packet top p a) := by
  unfold pairCode ActualFullLabelPairGuards.packet
  by_cases hm : p.maximum < top
  · rw [if_pos (show max (encodePair p).1.1 (encodePair p).2.1 < top from hm),if_pos hm]
    exact lowerPairEq p a
  · rw [if_neg (show ¬ max (encodePair p).1.1 (encodePair p).2.1 < top from hm),if_neg hm]
    exact topEq p.1.field p.2.field p.1.rank p.2.rank a

theorem exactPairCode : ExactPairCode := pairCodeEq

theorem compileCodeEq (top : Nat) : ∀ (ps : List Pair) (as : List Answer),
    compileCode top (ps.map encodePair) (as.map Answer.code) = encodePacket (compile top ps as)
  | [],[] => rfl
  | p :: ps,a :: as => by
    show appendCode (pairCode top (encodePair p) a.code)
        (compileCode top (ps.map encodePair) (as.map Answer.code)) =
      encodePacket (ActualPreparedSlotAppend.append (ActualFullLabelPairGuards.packet top p a)
        (compile top ps as))
    rw [pairCodeEq,compileCodeEq top ps as]
    exact appendCodeEq _ _
  | [],_ :: _ => rfl
  | _ :: _,[] => rfl

theorem exactCompileCode : ExactCompileCode := compileCodeEq

theorem orderedPairsEq (ls : List Label) :
    orderedPairs (ls.map encodeLabel) = (pairs ls).map encodePair := by
  first
    | (unfold orderedPairs pairs
       rw [List.flatMap_map,List.map_flatMap]
       congr 1
       funext l
       rw [List.map_map,List.map_map]
       rfl)
    | simp [orderedPairs,pairs,encodePair,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]

theorem guardCodeEq (top : Nat) (grouped : List WeightedOperand) (a : List Answer) :
    guardCode top ((labels grouped).map encodeLabel) (a.map Answer.code) =
      encodePacket (StageCallbackCanonicalRoutes.guard top grouped a) := by
  unfold guardCode
  rw [orderedPairsEq]
  exact compileCodeEq top (pairs (labels grouped)) a

theorem exactGuardCode : ExactGuardCode := guardCodeEq

#print axioms exactGuardCode

end LogicLineages.PermittedControl.StageCallbackGuardRender
