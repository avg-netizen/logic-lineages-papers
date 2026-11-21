module
public import LogicLineages.PermittedControl.ShortFieldPreprocessingTargets
import LogicLineages.PermittedControl.ThresholdNoteCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

private theorem rawShortGapLength_primrec : Primrec rawShortGapLength := by
  have hpred : Primrec (fun n : Nat => n - 1) := Primrec.nat_sub.comp Primrec.id (Primrec.const 1)
  have hu := Primrec.unpair.comp hpred
  have he := Primrec.fst.comp hu
  have hu' := Primrec.unpair.comp (Primrec.snd.comp hu)
  have hc := Primrec.fst.comp hu'
  have ht := Primrec.snd.comp hu'
  have htest := (Primrec.eq.comp he (Primrec.const (rawNoteEncode (NONote.ofNat 1).1))).and
    (Primrec.eq.comp ht (Primrec.const 0))
  refine (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite htest (Primrec.succ.comp hc) (Primrec.const 0))).of_eq ?_
  intro n
  cases n with
  | zero => rfl
  | succ n => simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one, rawShortGapLength]

theorem shortFieldPreprocessingEffective : ShortFieldPreprocessingEffective := by
  have hgap : Primrec₂ shortGapLengthCode :=
    rawShortGapLength_primrec.comp ordinalSubCodeEffective
  have hl : Primrec (fun p : Nat × Nat × Nat => p.1) := Primrec.fst
  have hm : Primrec (fun p : Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun p : Nat × Nat × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hk := hgap.comp hl hm
  have hn : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  refine ⟨rawShortGapLength_primrec,hgap,?_,?_,?_⟩
  · exact Primrec.ite (Primrec.eq.comp hk (Primrec.const 0)) (Primrec.const 0)
      (Primrec.succ.comp (Primrec.nat_add.comp ha hk))
  · exact Primrec.nat_max.comp (hn.comp hl)
      (Primrec.nat_max.comp (Primrec.nat_add.comp (hn.comp hm) (Primrec.const 3))
        (Primrec.nat_max.comp (Primrec.const 1) ha))
  · intro lam mu B
    simp only [shortFieldTail,shortFieldTailCode,normal_norm_code]

end LogicLineages.PermittedControl.FieldComparison
