module
public import LogicLineages.PermittedControl.OriginalPrintedRawConditionalQueryTargets
import LogicLineages.PermittedControl.OriginalPrintedRawFamilyFrontendPrimitiveProof
import LogicLineages.PermittedControl.ActualBitFamilyRawDriverComputableProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawConditionalQuery
open OriginalPrintedRawFamilyFrontend (Args familyCode originalRawFamilyFrontendEffectivity)
open ActualBitFamilyRawLayout (RawFamily)
open ActualBitFamilyRawDriver (solve exactDriverEffectivity)

theorem originalRawConditionalQueryEffectivity : OriginalRawConditionalQueryEffectivity := by
  intro f bound high hf hb hh
  have front : Computable familyCode := (show Primrec familyCode from originalRawFamilyFrontendEffectivity).to_comp
  have driver : Computable (solve f bound high) := exactDriverEffectivity f bound high hf hb hh
  have post : Computable₂ (fun (_ : Args) (raw : RawFamily) => solve f bound high raw) :=
    (driver.comp Computable.snd).to₂
  exact Computable.option_map front post

end LogicLineages.PermittedControl.OriginalPrintedRawConditionalQuery
