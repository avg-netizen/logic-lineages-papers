module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCodePrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedStructurePrimrecProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangePrimrecProof
open Source NumberedRewriteReduction NumberedAuxiliaryCoding NumberedExchangeCode

theorem packedCalibration : NumberedExchangePrimrecTargets.ActualPackedCalibration :=
  NumberedExchangeCalibrationProof.packedCalibration

theorem codeExchangePrimitive : NumberedExchangePrimrecTargets.ActualCodeExchangePrimitive :=
  NumberedExchangeCodePrimrecProof.codeExchangePrimitive

theorem exchangeTestPrimitive : NumberedExchangePrimrecTargets.ActualExchangeTestPrimitive := by
  intro n arity Gamma
  let Input := (List (Fin n) × List Ty) ×
    Packed (Fin n) arity Gamma × Packed (Fin n) arity Gamma
  have hq : Primrec (fun p : Input => packedCode p.2.1) :=
    (NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma).comp
      (Primrec.fst.comp Primrec.snd)
  have hr : Primrec (fun p : Input => packedCode p.2.2) :=
    (NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma).comp
      (Primrec.snd.comp Primrec.snd)
  have ht : Primrec (fun p : Input =>
      decide ((packedCode p.2.1).1 = (packedCode p.2.2).1)) :=
    (Primrec.eq.comp (Primrec.fst.comp hq) (Primrec.fst.comp hr)).decide
  have hc : Primrec (fun p : Input =>
      codeExchange arity p.1.1 p.1.2 (packedCode p.2.1).2 (packedCode p.2.2).2) :=
    (codeExchangePrimitive n arity).comp
      (Primrec.fst.pair ((Primrec.snd.comp hq).pair (Primrec.snd.comp hr)))
  have hp : Primrec (fun p : Input =>
      packedCodeExchange arity p.1.1 p.1.2 (packedCode p.2.1) (packedCode p.2.2)) :=
    Primrec.and.comp ht hc
  exact hp.of_eq (fun p => packedCalibration (Fin n) inferInstance arity Gamma
    p.1.1 p.1.2 p.2.1 p.2.2)

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangePrimrecProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangePrimrecProof
