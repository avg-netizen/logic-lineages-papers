module
public import LogicLineages.PersistentMarking.NumberedWindowPositiveFiberCalibrationTargets
import LogicLineages.PersistentMarking.NumberedWindowAddressProgramProof
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowPositiveFiberProjectionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowAddressAlgorithm NumberedWindowAddressProgramProof (addressPrim)
open NumberedWindowFieldAlgorithm (pack)
open NumberedWindowPositiveFiberCalibrationTargets

private theorem packPrim : Primrec pack := by
  obtain ⟨p,h⟩ := NumberedWindowFieldProgramChecks.exact_OrderedFieldPrograms.1
  apply ((Proof.primitiveEvaluation 1 p).comp
    (Primrec.vector_cons.comp Primrec.encode (Primrec.const List.Vector.nil))).of_eq
  exact h

private theorem contextPrim : Primrec contextField :=
  (Primrec.option_map₁ (packPrim.comp (Primrec.fst : Primrec (Prod.fst : Address → List Nat)))).comp addressPrim

private theorem resultPrim : Primrec resultField :=
  (Primrec.option_map₁ (Primrec.fst.comp (Primrec.snd : Primrec (Prod.snd : Address → Nat × Nat)))).comp
    addressPrim

theorem projectionPrograms : ProjectionPrograms := by
  obtain ⟨ctx,hctx⟩ := (Proof.unaryCorrespondence _).mp (Primrec.encode.comp contextPrim)
  obtain ⟨ty,hty⟩ := (Proof.unaryCorrespondence _).mp (Primrec.encode.comp resultPrim)
  exact ⟨ctx,ty,hctx,hty⟩
end LogicLineages.PersistentMarking.NumberedWindowPositiveFiberProjectionProof
