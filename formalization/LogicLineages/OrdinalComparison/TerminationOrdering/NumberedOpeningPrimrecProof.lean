module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedArgumentAppendPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectOperationsSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOpeningPrimrecProof
open Source NumberedAuxiliaryCoding NumberedDirectOperations NumberedAuxiliaryShift
open NumberedArgumentAppendPrimrecProof NumberedSyntaxBoundsPrimrecSupportProof

attribute [local irreducible] Primrec shiftCode appendArgumentCode

theorem shiftBinaryPrimitive (n : Nat) : Primrec₂ (@shiftCode (Fin n)) :=
  (NumberedAuxiliaryShiftPrimrecProof.codeShiftPrimitive n).to₂

theorem rawOpeningPrimitive : NumberedDirectOperationsTargets.ActualRawOpeningPrimitive := by
  intro n
  have h2 : Primrec (fun p : OpenData (Fin n) => p.2.2) := Primrec.snd.comp Primrec.snd
  have h3 := Primrec.snd.comp h2
  have h4 := Primrec.snd.comp h3
  have h5 := Primrec.snd.comp h4
  have hs : Primrec (fun p : OpenData (Fin n) => p.2.2.1) := Primrec.fst.comp h2
  have hb : Primrec (fun p : OpenData (Fin n) => shiftCode 0 p.2.2.2.2.1) :=
    (shiftBinaryPrimitive n).comp (Primrec.const 0) (Primrec.fst.comp h4)
  have he : Primrec (fun p : OpenData (Fin n) => shiftCode 0 p.2.2.2.2.2.2) :=
    (shiftBinaryPrimitive n).comp (Primrec.const 0) (Primrec.snd.comp h5)
  have hf : Primrec (fun p : OpenData (Fin n) => Code.argumentsCons p.2.2.1 (Code.var 0) Code.argumentsNil) :=
    (NumberedCodeAssemblyPrimrecProof.argumentsConsPrimitive n).comp
      (hs.pair ((Primrec.const (Code.var 0)).pair (Primrec.const Code.argumentsNil)))
  have htypes : Primrec (fun p : OpenData (Fin n) => p.2.2.2.2.2.1++[p.2.2.1]) :=
    Primrec.list_append.comp (Primrec.fst.comp h5) (singletonPrimitive hs)
  have hextras : Primrec (fun p : OpenData (Fin n) =>
      appendArgumentCode (shiftCode 0 p.2.2.2.2.2.2) (Code.argumentsCons p.2.2.1 (Code.var 0) Code.argumentsNil)) :=
    (argumentAppendPrimitive n).comp he hf
  have hd : Primrec (fun p : OpenData (Fin n) =>
      (p.1,p.2.1,p.2.2.2.1,shiftCode 0 p.2.2.2.2.1,p.2.2.2.2.2.1++[p.2.2.1],
        appendArgumentCode (shiftCode 0 p.2.2.2.2.2.2) (Code.argumentsCons p.2.2.1 (Code.var 0) Code.argumentsNil))) :=
    Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair ((Primrec.fst.comp h3).pair
      (hb.pair (htypes.pair hextras))))
  exact (NumberedCodeAssemblyPrimrecProof.numberedPrimitive n).comp hd

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOpeningPrimrecProof
