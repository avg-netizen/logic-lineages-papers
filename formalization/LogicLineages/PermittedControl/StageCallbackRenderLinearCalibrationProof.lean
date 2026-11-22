module
public import LogicLineages.PermittedControl.StageCallbackRenderLinearTargets
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingTapeProof

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackRender
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand LowerOperandCode PreparedPacketCode)
open RawPacketAlgebra (encodePacket)
open StageCallbackRawLevel (orderCode)
open MixedSameRankResidue (WeightedOperand WeightedCode encodeWeighted)
open ActualCanonicalOperandGrouping (groupRaw groupTyped exactCanonicalTape)
open ActualCanonicalTerminalTruth (canonicalPacket)
open ActualRawSignedStaticCeiling (RawSyntax encodeSyntax)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualSyntaxLinearTerminal (lower slope names termsTable termsRow)
open OriginalMatrixLinearRowFormula (testFormula choosePolarity)

/-- The rank is the second component of every operand code. -/
theorem rankCode (t : WeightedOperand) : (encodeWeighted t).2.2.1 = t.2.rank := by
  rcases t with ⟨w,op⟩
  cases op <;> rfl

theorem lowerExact (top : Nat) (ts : List WeightedOperand) :
    lowerCode top (ts.map encodeWeighted) = (lower top ts).map encodeWeighted := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    show (if (encodeWeighted t).2.2.1 < top then
        encodeWeighted t :: lowerCode top (ts.map encodeWeighted)
      else lowerCode top (ts.map encodeWeighted)) = _
    rw [ih,rankCode]
    by_cases h : t.2.rank < top
    · rw [if_pos h]
      simp [lower,List.filter_cons,h]
    · rw [if_neg h]
      simp [lower,List.filter_cons,h]

theorem slopeExact (top : Nat) (ts : List WeightedOperand) :
    slopeCode top (ts.map encodeWeighted) = slope top ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    show (if (encodeWeighted t).2.2.1 = top then t.1 + slopeCode top (ts.map encodeWeighted)
      else slopeCode top (ts.map encodeWeighted)) =
      (if t.2.rank = top then t.1 + slope top ts else slope top ts)
    rw [ih,rankCode]

theorem namesFold (ts : List WeightedOperand) :
    ∀ (j : Nat) (acc : List (Int × NormalForm.Code.ItemData)),
      (ts.map encodeWeighted).foldl
          (fun st t => (st.1+1,st.2 ++ [(t.1,((0 : Nat),st.1,(0 : Int),(0 : Int)))])) (j,acc) =
        (j + ts.length,acc ++ (names j ts).map (fun a => (a.1,a.2.data))) := by
  induction ts with
  | nil =>
    intro j acc
    show (j,acc) = (j + 0,acc ++ [])
    rw [Nat.add_zero,List.append_nil]
  | cons t ts ih =>
    intro j acc
    show (ts.map encodeWeighted).foldl
        (fun st t => (st.1+1,st.2 ++ [(t.1,((0 : Nat),st.1,(0 : Int),(0 : Int)))]))
        (j+1,acc ++ [(t.1,((0 : Nat),j,(0 : Int),(0 : Int)))]) = _
    rw [ih]
    refine Prod.ext ?_ ?_
    · show j + 1 + ts.length = j + (ts.length + 1)
      omega
    · exact (List.append_assoc _ _ _).trans rfl

theorem namesExact (i : Nat) (ts : List WeightedOperand) :
    namesCode i (ts.map encodeWeighted) = (names i ts).map (fun a => (a.1,a.2.data)) :=
  (congrArg Prod.snd (namesFold ts i [])).trans rfl

theorem rowExact (top : Nat) (c : Int) (ts : List WeightedOperand) :
    rowCode top c (ts.map encodeWeighted) = NormalForm.rowData (termsRow top c ts) := by
  show (c,(slopeCode top (ts.map encodeWeighted),((0 : Nat),(0 : Nat),(0 : Int),(0 : Int))) ::
      namesCode 1 (lowerCode top (ts.map encodeWeighted))) =
    (c,(slope top ts,((0 : Nat),(0 : Nat),(0 : Int),(0 : Int))) ::
      (names 1 (lower top ts)).map (fun a => (a.1,a.2.data)))
  rw [slopeExact,lowerExact,namesExact]

theorem rowScaleData (z : Int) (r : NormalForm.Row) :
    NormalForm.rowData (LinearRows.rowScale z r) =
      LinearRows.Code.rowScale z (NormalForm.rowData r) := by
  simp [NormalForm.rowData,LinearRows.rowScale,LinearRows.Code.rowScale]

theorem testExact (test : OrderTest) (r : NormalForm.Row) :
    testCode (orderCode test) (NormalForm.rowData r) = (testFormula test.test r).encode := by
  cases test with
  | equalZero =>
    show LinearRows.Code.conjunction (atomCode (NormalForm.rowData r))
      (atomCode (LinearRows.Code.rowScale (-1) (NormalForm.rowData r))) = _
    rw [← rowScaleData]
    exact rfl
  | nonnegative => exact rfl
  | positive => exact rfl

theorem polarityExact (p : NormalForm.Formula) (positive : Bool) :
    polarityCode p.encode positive = (choosePolarity p positive).encode := by
  cases positive <;> rfl

theorem exactLinearCode : ExactLinearCode := by
  intro top s test positive
  have grouped : groupRaw (s.terms.map encodeWeighted) = (groupTyped s.terms).map encodeWeighted :=
    (exactCanonicalTape.1 s.terms).symm
  have table : ((lower top (groupTyped s.terms)).map encodeWeighted).map Prod.snd =
      (termsTable top (groupTyped s.terms)).map LowerOperand.code := by
    simp [termsTable,List.map_map,Function.comp_def,encodeWeighted]
  show (Encodable.encode ((lowerCode top (groupRaw (s.terms.map encodeWeighted))).map Prod.snd),
      polarityCode (testCode (orderCode test)
        (rowCode top s.constant (groupRaw (s.terms.map encodeWeighted)))) positive) =
    (Encodable.encode ((termsTable top (groupTyped s.terms)).map LowerOperand.code),
      (choosePolarity (testFormula test.test
        (termsRow top s.constant (groupTyped s.terms))) positive).encode)
  rw [grouped,lowerExact,rowExact,testExact,polarityExact,table]

end LogicLineages.PermittedControl.StageCallbackRender
