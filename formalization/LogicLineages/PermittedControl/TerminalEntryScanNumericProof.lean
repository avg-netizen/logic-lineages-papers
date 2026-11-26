module
public import LogicLineages.PermittedControl.TerminalEntryScanTargets
import LogicLineages.PermittedControl.EncodedEvaluatorProof
import LogicLineages.OrdinalComparison.RawNormCode
import LogicLineages.OrdinalComparison.RawSplitProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

private theorem terminal_test_computable (f : Nat → Nat) (hf : Computable f) :
    Computable (fun p : (Nat × Nat) × Nat => terminalScanTest f p.1.1 p.1.2 p.2) := by
  have hstate : Computable (fun p : (Nat × Nat) × Nat => encodedStatesWith f p.1.1 p.2) :=
    (encodedStates_computable f hf).comp (Computable.fst.comp Computable.fst) Computable.snd
  have hsplit : Computable rawSplitCode := (Primrec.nat_iff.mpr rawSplitPrimitiveRecursive).to_comp
  have hlimit : Computable (fun n : Nat => (rawSplitCode n).unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).to_comp.comp hsplit
  exact Primrec.eq.decide.to_comp.comp (hlimit.comp hstate) (Computable.snd.comp Computable.fst)

private abbrev PrefixArgs := Nat × Nat × Nat

private def prefixBase (f : Nat → Nat) (p : PrefixArgs) : Nat :=
  if terminalScanTest f p.1 p.2.1 0 then 1 else 0

private def prefixStep (f : Nat → Nat) (p : PrefixArgs) (s : Nat × Nat) : Nat :=
  if s.2 = 0 then
    if terminalScanTest f p.1 p.2.1 (s.1+1) then s.1+2 else 0
  else s.2

private theorem prefixBase_computable (f : Nat → Nat) (hf : Computable f) :
    Computable (prefixBase f) := by
  have hn : Computable (fun p : PrefixArgs => p.1) := Computable.fst
  have hm : Computable (fun p : PrefixArgs => p.2.1) := Computable.fst.comp Computable.snd
  have ht := (terminal_test_computable f hf).comp ((hn.pair hm).pair (Computable.const 0))
  exact (Computable.cond ht (Computable.const 1) (Computable.const 0)).of_eq (fun p => by
    change cond (terminalScanTest f p.1 p.2.1 0) 1 0 = prefixBase f p
    cases h : terminalScanTest f p.1 p.2.1 0 <;> simp [prefixBase,h])

private theorem prefixStep_computable (f : Nat → Nat) (hf : Computable f) :
    Computable₂ (prefixStep f) := by
  have hn : Computable (fun p : PrefixArgs × (Nat × Nat) => p.1.1) :=
    Computable.fst.comp Computable.fst
  have hm : Computable (fun p : PrefixArgs × (Nat × Nat) => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hi : Computable (fun p : PrefixArgs × (Nat × Nat) => p.2.1) :=
    Computable.fst.comp Computable.snd
  have ho : Computable (fun p : PrefixArgs × (Nat × Nat) => p.2.2) :=
    Computable.snd.comp Computable.snd
  have hs := Primrec.succ.to_comp.comp hi
  have hss := Primrec.succ.to_comp.comp hs
  have ht := (terminal_test_computable f hf).comp ((hn.pair hm).pair hs)
  have hzero := Primrec.eq.decide.to_comp.comp ho (Computable.const 0)
  refine (Computable.cond hzero (Computable.cond ht hss (Computable.const 0)) ho).of_eq (fun p => ?_)
  change cond (decide (p.2.2 = 0))
    (cond (terminalScanTest f p.1.1 p.1.2.1 (p.2.1+1)) (p.2.1+2) 0) p.2.2 = prefixStep f p.1 p.2
  by_cases h : p.2.2 = 0 <;>
    cases ht' : terminalScanTest f p.1.1 p.1.2.1 (p.2.1+1) <;>
    simp [prefixStep,h,ht']

theorem boundedTerminalEntryIndex_computable (f : Nat → Nat) (hf : Computable f) :
    Computable (fun p : Nat × Nat × Nat => boundedTerminalEntryIndex f p.1 p.2.1 p.2.2) := by
  have hT : Computable (fun p : PrefixArgs => p.2.2) := Computable.snd.comp Computable.snd
  have heq (p : PrefixArgs) (T : Nat) :
      Nat.rec (prefixBase f p) (fun i old => prefixStep f p (i,old)) T =
        boundedTerminalEntryIndex f p.1 p.2.1 T := by
    induction T with
    | zero => rfl
    | succ T ih =>
      change prefixStep f p (T,Nat.rec (prefixBase f p) (fun i old => prefixStep f p (i,old)) T) = _
      rw [ih] <;> rfl
  exact (Computable.nat_rec hT (prefixBase_computable f hf) (prefixStep_computable f hf)).of_eq
    (fun p => heq p p.2.2)

theorem terminalScanAt_computable (f : Nat → Nat) (hf : Computable f) :
    Computable₂ (terminalScanAt f) := by
  let α := (Nat × Nat) × Nat
  have hargs : Computable (fun p : α => (p.1.1,p.1.2,p.2)) :=
    (Computable.fst.comp Computable.fst).pair ((Computable.snd.comp Computable.fst).pair Computable.snd)
  have hidx := (boundedTerminalEntryIndex_computable f hf).comp hargs
  have hn : Computable (fun p : α × Nat => p.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hstate := (encodedStates_computable f hf).comp hn Computable.snd
  have hnorm : Computable rawNormCode := (Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).to_comp
  have hout : Computable₂ (fun (_p : α) (i : Nat) =>
      some (some (rawNormCode (encodedStatesWith f _p.1.1 i),i))) :=
    Computable.option_some.comp (Computable.option_some.comp ((hnorm.comp hstate).pair Computable.snd))
  refine (Computable.nat_casesOn hidx (Computable.const (some none)) hout).of_eq ?_
  intro p
  change Nat.casesOn (boundedTerminalEntryIndex f p.1.1 p.1.2 p.2)
    (some none) (fun i => some (some (rawNormCode (encodedStatesWith f p.1.1 i),i))) =
      terminalScanAt f p.1 p.2
  unfold terminalScanAt
  cases boundedTerminalEntryIndex f p.1.1 p.1.2 p.2 <;> rfl

end LogicLineages.PermittedControl
