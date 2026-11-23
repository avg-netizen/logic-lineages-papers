module
public import LogicLineages.PermittedControl.PolicySuppliedCodeMacroInterpreterTargets
import LogicLineages.StandardControlCurrent.PolicyShapeProgramsProof

public section
namespace LogicLineages.PermittedControl.PolicySuppliedCodeMacro
open OrdinalComparison.Source.AdmissibleSum
open StandardControlCurrent

private theorem decodeExpandProgram :
    Primrec (fun x : Nat × List Nat => decodeExpand x.1 x.2) := by
  have hdecode : Primrec (fun x : Nat × List Nat =>
      (Encodable.decode x.1 : Option (List Bool))) :=
    Primrec.decode.comp Primrec.fst
  have hexpand : Primrec₂ (fun x : Nat × List Nat => fun script : List Bool =>
      PolicyShape.expandCode script x.2) :=
    (PolicyShapeProgramsProof.expandProgram.comp
      (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))).to₂
  exact Primrec.option_bind hdecode hexpand

/-- One partially recursive function takes the program itself as input. -/
theorem macroPartrec : MacroPartrec := by
  have hcode : Computable (fun a : Args => a.1) := Computable.fst
  have htag : Computable (fun a : Args => a.2.1) :=
    Computable.fst.comp Computable.snd
  have harity : Computable (fun a : Args => a.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hinput : Computable (fun a : Args => Nat.pair a.2.1 a.2.2.1) :=
    Primrec₂.natPair.to_comp.comp htag harity
  have hxs : Computable (fun a : Args => a.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have heval : Partrec (fun a : Args => a.1.eval (Nat.pair a.2.1 a.2.2.1)) :=
    Nat.Partrec.Code.eval_part.comp hcode hinput
  have hfinish : Computable₂ (fun a : Args => fun z : Nat =>
      decodeExpand z a.2.2.2) :=
    (decodeExpandProgram.to_comp.comp
      (Computable.snd.pair (hxs.comp Computable.fst))).to₂
  exact heval.map hfinish

/-- Realization of the selector suffices for exact returned expansion and
termination. No premise about the compiler's result is used. -/
theorem exactMacroCalibration : ExactMacroCalibration := by
  intro e p he tag n xs
  change ((e.eval (Nat.pair tag n)).map (fun z => decodeExpand z xs)) =
    Part.some (PolicyShape.macroCode p tag n xs)
  rw [he tag n]
  simp only [Part.map_some, decodeExpand, Encodable.encodek, Option.bind_some,
    PolicyShape.macroCode]

theorem fullSuppliedCodeMacro : FullSuppliedCodeMacro :=
  ⟨macroPartrec, exactMacroCalibration⟩

#print axioms macroPartrec
#print axioms exactMacroCalibration
#print axioms fullSuppliedCodeMacro

end LogicLineages.PermittedControl.PolicySuppliedCodeMacro
