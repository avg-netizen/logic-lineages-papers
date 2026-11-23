module
public import LogicLineages.PermittedControl.ClosedOrdinaryFieldTargets
import LogicLineages.PermittedControl.UniformNearClosedBlockScanProof
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
attribute [local irreducible] fixedEntryClosedScan

variable {α : Type} [Primcodable α]

theorem iterateParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable (fun x : α × (Nat × Nat) => (F x.1)^[x.2.1] x.2.2) := by
  have hstep : Computable₂ (fun (x : α × (Nat × Nat)) (p : Nat × Nat) => F x.1 p.2) :=
    hF.comp (Computable.fst.comp Computable.fst) (Computable.snd.comp Computable.snd)
  apply (Computable.nat_rec (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)
    hstep).of_eq
  rintro ⟨a,n,y⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    change Nat.rec y (fun _ v => F a v) (n+1) = (F a)^[n+1] y
    rw [Function.iterate_succ_apply']
    exact congrArg (F a) ih

theorem entryResultParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable (fun x : α × FixedEntryClosedArgs => closedProperEntryResult (F x.1) x.2) := by
  have hguard : Computable (fun x : α × FixedEntryClosedArgs => closedProperEntryGuard x.2) :=
    closedProperEntryDomainExact.1.to_comp.comp Computable.snd
  exact (Computable.cond hguard (closedScanParam F hF) (Computable.const none)).of_eq
    (fun x => by cases h : closedProperEntryGuard x.2 <;> simp [closedProperEntryResult,h])

theorem valueFieldParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable (fun x : α × (LongFieldCode × Nat) => closedOrdinaryValueField (F x.1) x.2.1 x.2.2) := by
  have hc : Computable (fun x : α × (LongFieldCode × Nat) => x.1) := Computable.fst
  have htag : Computable (fun x : α × (LongFieldCode × Nat) => x.2.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.snd)
  have ha : Computable (fun x : α × (LongFieldCode × Nat) => x.2.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.snd))
  have hl : Computable (fun x : α × (LongFieldCode × Nat) => x.2.1.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.snd)))
  have hm : Computable (fun x : α × (LongFieldCode × Nat) => x.2.1.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.snd)))
  have hx : Computable (fun x : α × (LongFieldCode × Nat) => x.2.2) := Computable.snd.comp Computable.snd
  have hit : Computable (fun x : α × (LongFieldCode × Nat) => (F x.1)^[x.2.1.2.1] x.2.2) := by
    have h := (iterateParam F hF).comp (hc.pair (ha.pair hx))
    exact h
  have hiterate : Computable (fun x : α × (LongFieldCode × Nat) => some (some ((F x.1)^[x.2.1.2.1] x.2.2))) :=
    Computable.option_some.comp (Computable.option_some.comp hit)
  have hentry : Computable (fun x : α × (LongFieldCode × Nat) =>
      closedProperEntryResult (F x.1) (x.2.1.2.2.1,x.2.1.2.2.2,x.2.2)) := by
    have h := (entryResultParam F hF).comp (hc.pair (hl.pair (hm.pair hx)))
    exact h
  have hv : Computable (fun q : ((α × (LongFieldCode × Nat)) × Option (Nat × Nat)) × (Nat × Nat) =>
      (F q.1.1.1)^[q.1.1.2.1.2.1] q.2.1) := by
    have q0 : Computable (fun q : ((α × (LongFieldCode × Nat)) × Option (Nat × Nat)) × (Nat × Nat) => q.1.1) :=
      Computable.fst.comp Computable.fst
    have qv : Computable (fun q : ((α × (LongFieldCode × Nat)) × Option (Nat × Nat)) × (Nat × Nat) => q.2.1) :=
      Computable.fst.comp Computable.snd
    have h := (iterateParam F hF).comp ((hc.comp q0).pair ((ha.comp q0).pair qv))
    exact h
  have hinner : Computable₂ (fun (x : α × (LongFieldCode × Nat)) (r : Option (Nat × Nat)) =>
      r.map (fun v => (F x.1)^[x.2.1.2.1] v.1)) := by
    have h := Computable.option_map Computable.snd hv.to₂
    exact h
  have hresult : Computable (fun x : α × (LongFieldCode × Nat) =>
      (closedProperEntryResult (F x.1) (x.2.1.2.2.1,x.2.1.2.2.2,x.2.2)).map
        (fun r => r.map (fun v => (F x.1)^[x.2.1.2.1] v.1))) := by
    have h := Computable.option_map hentry hinner
    exact h
  have hguard : Computable (fun x : α × (LongFieldCode × Nat) => decide (x.2.1.1 = 0)) :=
    Primrec.eq.decide.to_comp.comp htag (Computable.const 0)
  have hcond := Computable.cond hguard hiterate hresult
  refine hcond.of_eq (fun x => ?_)
  rcases x with ⟨c,⟨tag,a,lam,mu⟩,y⟩
  by_cases h : tag = 0 <;> simp [closedOrdinaryValueField,h]

theorem countFieldParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable (fun x : α × FixedEntryClosedArgs => closedOrdinaryCountField (F x.1) x.2) := by
  have hmap : Computable (fun r : Option (Nat × Nat) => r.map Prod.snd) :=
    Computable.option_map Computable.id (Computable.snd.comp Computable.snd)
  exact Computable.option_map (entryResultParam F hF) (hmap.comp Computable.snd).to₂

end LogicLineages.PermittedControl.UniformNearClosedBlock
