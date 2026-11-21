module
public import LogicLineages.PermittedControl.TerminalEntryScanTargets
import LogicLineages.PermittedControl.EntryEffectivityProof
import LogicLineages.OrdinalComparison.RawNormalProof
import LogicLineages.OrdinalComparison.RawSplitProof
import LogicLineages.OrdinalComparison.RawNotationCode

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

private theorem guard_primitive : Primrec terminalScanGuard := by
  have hn : Primrec rawNormalCode := Primrec.nat_iff.mpr rawNormalPrimitiveRecursive
  have hs : Primrec rawSplitCode := Primrec.nat_iff.mpr rawSplitPrimitiveRecursive
  have hfirst : Primrec (fun p : Nat × Nat => p.1) := Primrec.fst
  have hsecond : Primrec (fun p : Nat × Nat => p.2) := Primrec.snd
  have hlimcode : Primrec (fun p : Nat × Nat => (rawSplitCode p.2).unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (hs.comp hsecond))
  have hstart : PrimrecPred (fun p : Nat × Nat => rawNormalCode p.1 = 1) :=
    Primrec.eq.comp (hn.comp hfirst) (Primrec.const 1)
  have htarget : PrimrecPred (fun p : Nat × Nat => rawNormalCode p.2 = 1) :=
    Primrec.eq.comp (hn.comp hsecond) (Primrec.const 1)
  have hlimit : PrimrecPred (fun p : Nat × Nat => (rawSplitCode p.2).unpair.1 = p.2) :=
    Primrec.eq.comp hlimcode hsecond
  exact (hstart.and (htarget.and hlimit)).decide

private theorem limit_part_zero_or_limit (z : Ordinal.{0}) :
    actualLimitPart z = 0 ∨ Order.IsSuccLimit (actualLimitPart z) := by
  by_cases hz : z / Ordinal.omega0 = 0
  · exact Or.inl (by simp [actualLimitPart,hz])
  · exact Or.inr (Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 (pos_iff_ne_zero.mpr hz))

theorem terminalEntryScanGuardExact : Targets.TerminalEntryScanGuardExact := by
  refine ⟨guard_primitive,?_⟩
  intro p
  constructor
  · intro h
    obtain ⟨hs,ht,hcode⟩ := of_decide_eq_true h
    have hnf := (rawNormalDecodeCorrect p.2).mp ht
    let mu : NONote := ⟨rawNoteDecode p.2,hnf⟩
    have hencode : rawNoteEncode mu.1 = p.2 := rawNoteEncodeDecode p.2
    have hlim := (split_code_eq mu mu).mp (by rw [hencode]; exact hcode)
    exact ⟨(rawNormalDecodeCorrect p.1).mp hs,hnf,
      by simpa only [hlim] using limit_part_zero_or_limit mu.1.repr⟩
  · rintro ⟨hs,ht,hlim⟩
    let mu : NONote := ⟨rawNoteDecode p.2,ht⟩
    have hencode : rawNoteEncode mu.1 = p.2 := rawNoteEncodeDecode p.2
    have hbetween : mu.1.repr < mu.1.repr + Ordinal.omega0 := by
      simpa only [add_zero] using (add_lt_add_iff_left mu.1.repr).mpr Ordinal.omega0_pos
    have hfix := (interval_iff_limitPart mu.1.repr mu.1.repr hlim).mp ⟨le_rfl,hbetween⟩
    have hcode := (split_code_eq mu mu).mpr hfix
    rw [hencode] at hcode
    exact decide_eq_true ⟨(rawNormalDecodeCorrect p.1).mpr hs,(rawNormalDecodeCorrect p.2).mpr ht,hcode⟩

end LogicLineages.PermittedControl
