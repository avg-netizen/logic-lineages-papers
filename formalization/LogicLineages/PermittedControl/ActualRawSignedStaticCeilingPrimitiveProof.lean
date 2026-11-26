module
public import LogicLineages.PermittedControl.ActualRawSignedStaticCeilingTargets
import LogicLineages.PermittedControl.ActualRawComparisonCeilingPrimitiveProof
import LogicLineages.PermittedControl.ActualBitFamilyRawReadCeilingPrimitiveProof
import LogicLineages.PermittedControl.ActualEffectiveGlobalTailPrimitiveProof
import LogicLineages.PermittedControl.ActualEffectiveTerminalSignBoundPrimitiveProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawSignedStaticCeiling
open MixedSameRankResidue (WeightedCode)
open ActualRawComparisonCeiling (budgetPrimitive)
open ActualBitFamilyRawReadCeiling (termsCode termsPrimitive)
open ActualEffectiveGlobalTail (inputTailCode)
open ActualEffectiveTerminalSignBound (inputSignBoundCode)

theorem commonPrimitive : Primrec (fun p : Nat × Nat × RawSyntax => commonCode p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × RawSyntax
  have B : Primrec (fun p : A => p.1) := Primrec.fst
  have r : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have terms : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have args := B.pair (r.pair terms)
  have reads := termsPrimitive.comp terms
  have tail := ActualEffectiveGlobalTail.codeEffectivity.2.2.comp args
  have comparison := budgetPrimitive.comp args
  exact (Primrec.nat_max.comp reads (Primrec.nat_max.comp tail comparison)).of_eq (fun _ => rfl)

theorem signPrimitive : Primrec (fun p : Nat × RawSyntax => signCode p.1 p.2) :=
  ActualEffectiveTerminalSignBound.codeEffectivity.2

theorem staticPrimitive : Primrec (fun p : Nat × Nat × RawSyntax => staticCode p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × RawSyntax
  have args : Primrec (fun p : A => p.2) := Primrec.snd
  have sign : Primrec (fun p : A => signCode p.2.1 p.2.2) := signPrimitive.comp args
  exact (Primrec.nat_max.comp commonPrimitive sign).of_eq (fun _ => rfl)

theorem exactRawSignedStaticEffectivity : ExactRawSignedStaticEffectivity :=
  ⟨commonPrimitive,signPrimitive,staticPrimitive⟩

end LogicLineages.PermittedControl.ActualRawSignedStaticCeiling
