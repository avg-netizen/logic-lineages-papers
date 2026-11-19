module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAccountTargets
public import LogicLineages.StandardControlCurrent.PolicyAssignmentRunPrograms
public import LogicLineages.OrdinalComparison.NumericCarrierDataPrimitiveProof
public import LogicLineages.OrdinalComparison.SourceCarrierMapCodeProof
public import LogicLineages.OrdinalComparison.GroundCaptureClosingCodePrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundAccountPrograms

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open AdmissibleSum

theorem carrierProgram (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun q : List Nat × Nat => CurrentGroundAccount.carrierCode p q.1 q.2) := by
  let S := List Nat × Nat
  have hΓ : Primrec (fun z : S => z.1) := Primrec.fst
  have hσ : Primrec (fun z : S => z.1.getD 0 0) :=
    (Primrec.list_getD 0).comp hΓ (Primrec.const 0)
  have hΔ : Primrec (fun z : S => z.1.getD 0 0 :: z.1) :=
    Primrec.list_cons.comp hσ hΓ
  have hsrc : Primrec (fun z : S => SourceAnnotationCode.operatorSource z.2) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have hrename := SourceCarrierMapCode.Proof.primitiveRecursive.comp
      ((Primrec.const true).pair ((Primrec.const 0).pair hsrc))
  have hsat := NumericCarrierData.Proof.primitiveRecursiveAlgorithms.2.2.1.comp
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd : Primrec (fun z : S => z.2)))) hrename
  have hw := GroundCaptureClosingCode.Proof.primitiveRecursiveAlgorithms.1.comp
    (hΔ.pair ((Primrec.const 0).pair hsat))
  have hv := (PolicyAssignmentRunPrograms.assignment p hp).comp (hΔ.pair hw).to_comp
  have hpriv := Primrec.list_cons.comp hσ (Primrec.list_cons.comp hσ (Primrec.const []))
  have hout : Primrec (fun z : S × List Nat =>
      ([z.1.1.getD 0 0,z.1.1.getD 0 0],
        GroundCaptureClosingCode.sourceCode (z.1.1.getD 0 0 :: z.1.1) 0
          (NumericCarrierData.saturateSource (SourceAnnotationCode.operatorArity z.1.2)
            (SourceCarrierMapCode.mapCode true 0 (SourceAnnotationCode.operatorSource z.1.2))),z.2)) :=
    (hpriv.comp Primrec.fst).pair ((hw.comp Primrec.fst).pair Primrec.snd)
  have h := Computable.option_map hv hout.to_comp.to₂
  apply h.of_eq
  intro z
  simp [CurrentGroundAccount.carrierCode,Option.map_eq_bind]

end LogicLineages.ControlSensitivityCurrent.CurrentGroundAccountPrograms
