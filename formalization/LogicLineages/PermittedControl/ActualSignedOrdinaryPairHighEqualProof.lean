module
public import LogicLineages.PermittedControl.ActualSignedOrdinaryPairHighTargets
import LogicLineages.PermittedControl.ActualSignedOrdinaryPairHighValueProof
import LogicLineages.PermittedControl.ActualSignedOrdinaryPairHighPaidProof
import LogicLineages.PermittedControl.HighFieldPreparedPacketShapeProof
import LogicLineages.PermittedControl.HighFieldComparisonActualProof
import LogicLineages.PermittedControl.HighFieldComparisonCalibrationProof
import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaShapeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSignedOrdinaryPairHigh
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open HighFieldPreparedPacket (constantFormula packetShape)
open OriginalMatrixLinearRowFormula (safePolarity)

theorem exactEqualRankSignedPair : ExactEqualRankSignedPair := by
  intro f B selected F G hF hG ρ rank c nz k positive
  let answer := sameForm (normalizeShortField F) (normalizeShortField G)
  let base := constantFormula 0 answer (request k c).1
  let bit := wantedBit k c positive
  refine ⟨rfl,safePolarity [] base (packetShape.2.1 0 answer (request k c).1) bit,?_⟩
  intro ν z paid θ
  have whereAt : θ rank = z := by simp [θ]
  have xTail : highFieldComparisonBoundCode B (longFieldCode F) (longFieldCode G) ≤ z :=
    (le_max_left _ _).trans paid
  have tail : highFieldComparisonBoundCode B (longFieldCode F) (longFieldCode G) ≤ min z z := by
    simpa only [min_self] using xTail
  obtain ⟨u,v,hvF,hvG,_,_,common,_⟩ :=
    highFieldComparisonActual f B selected F G hF hG z z tail
  have flags := (highFieldComparisonCalibration.2.2.2 F G z z).2.1 rfl
  have exactCode := flags.symm.trans (common rfl)
  have realAnswer : answer = numericalComparison u v :=
    congrArg (fun p : OrientedHighFormCode => p.2.2.1) exactCode
  have payF : normCode F ≤ θ rank :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (whereAt.symm ▸ paid))
  have payG : normCode G ≤ θ rank :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (whereAt.symm ▸ paid))
  have dF := originalDomain F (θ rank) hF payF
  have dG := originalDomain G (θ rank) hG payG
  have rF : LowerOperandActual f θ (.ordinary rank F) u := ⟨dF,by simpa only [whereAt] using hvF⟩
  have rG : LowerOperandActual f θ (.ordinary rank G) v := ⟨dG,by simpa only [whereAt] using hvG⟩
  refine ⟨dF,dG,bothLiteralHits f θ F G rank rank u v rF rG,?_⟩
  let slots := Function.update ν 0 z
  have baseMeaning : base.eval slots ↔ numericalComparison u v = (request k c).1 := by
    by_cases matchCode : numericalComparison u v = (request k c).1 <;>
      simp [base,constantFormula,flipHighComparisonAnswer,realAnswer,matchCode,NormalForm.Formula.eval]
  have same := exactSignedPairValue f θ F G rank rank u v c nz rF rG k positive
  exact (polarityMeaning base bit slots _ baseMeaning).trans same.symm

end LogicLineages.PermittedControl.ActualSignedOrdinaryPairHigh
