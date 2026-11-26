module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleTargets
import LogicLineages.PersistentMarking.NumberedWindowConcreteCheckersProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowFormulaCalibrationChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTuplePresentationProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAccessibilityRulesProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFormulaCalibrationTargets (Evaluates Interprets)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalAccessibilityTargets (Rules)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseTuple (CallbacksAt)
open NumberedWindowConcreteCheckersProgramChecks (exact_AllFourProgramWitnesses)
open NumberedWindowInternalSparseAddressPositiveNumericChecks (exact_ConcreteAddressPositive)
open NumberedWindowFormulaCalibrationChecks (exact_InterpretsEvaluatingPrograms)

def PresentationAt (xs : Entries) (s : Settings) (i j : Program 1) (r d : Program 3) : Prop :=
  Evaluates (checks xs s) i j r d ∧ Interprets (checks xs s) (data i j r d) ∧ Rules (data i j r d)

theorem rebuild (xs : Entries) (s : Settings) (i j : Program 1) (r d : Program 3)
    (values : Evaluates (checks xs s) i j r d) : PresentationAt xs s i j r d := by
  let S := data i j r d
  exact ⟨values,exact_InterpretsEvaluatingPrograms (checks xs s) i j r d values,
    ⟨actualOriginalMembershipEquation S,actualOriginalCarrierExtraction S,
      actualOriginalSuccessorClosure S,actualOriginalCertifiedSuccessorClosure S,
      actualOriginalAccessibilityIntroduction S⟩⟩

theorem select (xs : Entries) (s : Settings) :
    ∃ (i j cv tv : Program 1) (d : Program 3) (raw : Program 5) (least : Program 3),
      PresentationAt xs s i j (addressPositive cv tv raw least) d ∧
      CallbacksAt xs s cv tv raw least := by
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩,_,⟨d,hd⟩⟩ := exact_AllFourProgramWitnesses xs s
  obtain ⟨cv,tv,raw,least,hcv,htv,hr,hl,ha,hf,hp,had⟩ := exact_ConcreteAddressPositive xs s
  have values : Evaluates (checks xs s) i j (addressPositive cv tv raw least) d :=
    ⟨hi,hj,had,hd⟩
  exact ⟨i,j,cv,tv,d,raw,least,rebuild xs s i j (addressPositive cv tv raw least) d values,
    ⟨hcv,htv,hr,hl,ha,hf,hp⟩⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTuplePresentationProof
