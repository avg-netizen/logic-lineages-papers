module
public import LogicLineages.PermittedControl.ClosedOrdinaryFieldTargets
import LogicLineages.PermittedControl.EncodedEvaluatorProof
import LogicLineages.PermittedControl.TerminalEntryScanGuardProof
import LogicLineages.PermittedControl.TerminalEntryScanProgramProof
import LogicLineages.PermittedControl.FixedEntryClosedScanEffectiveProof
import LogicLineages.PermittedControl.ClosedOrdinaryFieldGuardProof
import LogicLineages.OrdinalComparison.RawNormCode
import LogicLineages.OrdinalComparison.RawSplitProof
import LogicLineages.OrdinalComparison.RawNormalProof
import Mathlib.Computability.RE

/-! Parametric copies of the per-control effectivity proofs of the entry
scan and the closed ordinary fields: the control is `F a` for a context
`a : α`, and computability is joint in `a`. Same constructions, same order,
with `hF.comp` in place of `hf.comp`. -/

public section
namespace LogicLineages.PermittedControl.UniformNearClosedBlock
open OrdinalComparison
open FieldComparison (closedProperEntryResult closedOrdinaryValueField closedOrdinaryCountField
  closedProperEntryGuard closedProperEntryDomainExact LongFieldCode)

attribute [local irreducible] rawSplitCode rawNormCode rawNormalCode encodedMaximumPredecessor
  encodedFiniteTest encodedFiniteValue Nat.unpair Nat.sqrt

variable {α : Type} [Primcodable α]

theorem stepParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable (fun x : α × Nat => encodedStepWith (F x.1) x.2) := by
  have hs : Primrec rawSplitCode := Primrec.nat_iff.mpr rawSplitPrimitiveRecursive
  have hl := (Primrec.fst.comp (Primrec.unpair.comp hs)).to_comp
  have hn : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have hM := encodedMaximumPredecessorPrimitiveRecursive.to_comp
  have ht := encodedFiniteAlgorithmsPrimitiveRecursive.1.to_comp
  have arg : Computable (fun x : α × Nat => x.2) := Computable.snd
  have fv : Computable (fun x : α × Nat => F x.1 (rawNormCode x.2)) :=
    hF.comp Computable.fst (hn.to_comp.comp arg)
  exact (Computable.cond (ht.comp arg) arg (hM.comp (hl.comp arg) fv)).of_eq
    (fun x => by cases h : encodedFiniteTest x.2 <;> simp [encodedStepWith,h])

theorem statesParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable (fun x : α × (Nat × Nat) => encodedStatesWith (F x.1) x.2.1 x.2.2) := by
  have hs := stepParam F hF
  have hstep : Computable₂ (fun (x : α × (Nat × Nat)) (v : Nat × Nat) => encodedStepWith (F x.1) v.2) :=
    hs.comp ((Computable.fst.comp Computable.fst).pair (Computable.snd.comp Computable.snd))
  apply (Computable.nat_rec (Computable.snd.comp Computable.snd) (Computable.fst.comp Computable.snd)
    hstep).of_eq
  rintro ⟨a,n,k⟩
  induction k with
  | zero => rfl
  | succ k ih => simpa only [Nat.rec_add_one,encodedStatesWith,Function.iterate_succ_apply',ih]

theorem testParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable (fun x : α × ((Nat × Nat) × Nat) => terminalScanTest (F x.1) x.2.1.1 x.2.1.2 x.2.2) := by
  have hstate : Computable (fun x : α × ((Nat × Nat) × Nat) => encodedStatesWith (F x.1) x.2.1.1 x.2.2) :=
    (statesParam F hF).comp (Computable.fst.pair
      ((Computable.fst.comp (Computable.fst.comp Computable.snd)).pair (Computable.snd.comp Computable.snd)))
  have hsplit : Computable rawSplitCode := (Primrec.nat_iff.mpr rawSplitPrimitiveRecursive).to_comp
  have hlimit : Computable (fun n : Nat => (rawSplitCode n).unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).to_comp.comp hsplit
  exact Primrec.eq.decide.to_comp.comp (hlimit.comp hstate)
    (Computable.snd.comp (Computable.fst.comp Computable.snd))

private def prefixBaseP (F : α → Nat → Nat) (x : α × (Nat × Nat × Nat)) : Nat :=
  if terminalScanTest (F x.1) x.2.1 x.2.2.1 0 then 1 else 0

private def prefixStepP (F : α → Nat → Nat) (x : α × (Nat × Nat × Nat)) (s : Nat × Nat) : Nat :=
  if s.2 = 0 then
    if terminalScanTest (F x.1) x.2.1 x.2.2.1 (s.1+1) then s.1+2 else 0
  else s.2

private theorem prefixBaseP_computable (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable (prefixBaseP F) := by
  have hn : Computable (fun x : α × (Nat × Nat × Nat) => x.2.1) := Computable.fst.comp Computable.snd
  have hm : Computable (fun x : α × (Nat × Nat × Nat) => x.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have ht := (testParam F hF).comp (Computable.fst.pair ((hn.pair hm).pair (Computable.const 0)))
  exact (Computable.cond ht (Computable.const 1) (Computable.const 0)).of_eq (fun x => by
    change cond (terminalScanTest (F x.1) x.2.1 x.2.2.1 0) 1 0 = prefixBaseP F x
    cases h : terminalScanTest (F x.1) x.2.1 x.2.2.1 0 <;> simp [prefixBaseP,h])

private theorem prefixStepP_computable (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable₂ (prefixStepP F) := by
  let Q := (α × (Nat × Nat × Nat)) × (Nat × Nat)
  have ha : Computable (fun p : Q => p.1.1) := Computable.fst.comp Computable.fst
  have hn : Computable (fun p : Q => p.1.2.1) := Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hm : Computable (fun p : Q => p.1.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hi : Computable (fun p : Q => p.2.1) := Computable.fst.comp Computable.snd
  have ho : Computable (fun p : Q => p.2.2) := Computable.snd.comp Computable.snd
  have hs := Primrec.succ.to_comp.comp hi
  have hss := Primrec.succ.to_comp.comp hs
  have ht := (testParam F hF).comp (ha.pair ((hn.pair hm).pair hs))
  have hzero := Primrec.eq.decide.to_comp.comp ho (Computable.const 0)
  refine (Computable.cond hzero (Computable.cond ht hss (Computable.const 0)) ho).of_eq (fun p => ?_)
  change cond (decide (p.2.2 = 0))
    (cond (terminalScanTest (F p.1.1) p.1.2.1 p.1.2.2.1 (p.2.1+1)) (p.2.1+2) 0) p.2.2 = prefixStepP F p.1 p.2
  by_cases h : p.2.2 = 0 <;>
    cases ht' : terminalScanTest (F p.1.1) p.1.2.1 p.1.2.2.1 (p.2.1+1) <;>
    simp [prefixStepP,h,ht']

theorem boundedParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable (fun x : α × (Nat × Nat × Nat) => boundedTerminalEntryIndex (F x.1) x.2.1 x.2.2.1 x.2.2.2) := by
  have hT : Computable (fun x : α × (Nat × Nat × Nat) => x.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have heq (x : α × (Nat × Nat × Nat)) (T : Nat) :
      Nat.rec (prefixBaseP F x) (fun i old => prefixStepP F x (i,old)) T =
        boundedTerminalEntryIndex (F x.1) x.2.1 x.2.2.1 T := by
    induction T with
    | zero => rfl
    | succ T ih =>
      change prefixStepP F x (T,Nat.rec (prefixBaseP F x) (fun i old => prefixStepP F x (i,old)) T) = _
      rw [ih] <;> rfl
  exact (Computable.nat_rec hT (prefixBaseP_computable F hF) (prefixStepP_computable F hF)).of_eq
    (fun x => heq x x.2.2.2)

theorem scanAtParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable (fun x : α × ((Nat × Nat) × Nat) => terminalScanAt (F x.1) x.2.1 x.2.2) := by
  let A := α × ((Nat × Nat) × Nat)
  have hargs : Computable (fun x : A => (x.1,(x.2.1.1,x.2.1.2,x.2.2))) :=
    Computable.fst.pair ((Computable.fst.comp (Computable.fst.comp Computable.snd)).pair
      ((Computable.snd.comp (Computable.fst.comp Computable.snd)).pair (Computable.snd.comp Computable.snd)))
  have hidx := (boundedParam F hF).comp hargs
  have hstate : Computable (fun p : A × Nat => encodedStatesWith (F p.1.1) p.1.2.1.1 p.2) :=
    (statesParam F hF).comp ((Computable.fst.comp Computable.fst).pair
      ((Computable.fst.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))).pair Computable.snd))
  have hnorm : Computable rawNormCode := (Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).to_comp
  have hout : Computable₂ (fun (x : A) (i : Nat) =>
      some (some (rawNormCode (encodedStatesWith (F x.1) x.2.1.1 i),i))) :=
    Computable.option_some.comp (Computable.option_some.comp ((hnorm.comp hstate).pair Computable.snd))
  refine (Computable.nat_casesOn hidx (Computable.const (some none)) hout).of_eq ?_
  intro x
  change Nat.casesOn (boundedTerminalEntryIndex (F x.1) x.2.1.1 x.2.1.2 x.2.2)
    (some none) (fun i => some (some (rawNormCode (encodedStatesWith (F x.1) x.2.1.1 i),i))) =
      terminalScanAt (F x.1) x.2.1 x.2.2
  unfold terminalScanAt
  cases boundedTerminalEntryIndex (F x.1) x.2.1.1 x.2.1.2 x.2.2 <;> rfl

end LogicLineages.PermittedControl.UniformNearClosedBlock
