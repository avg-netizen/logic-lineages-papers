module
public import LogicLineages.StandardControlCurrent.PolicyAbstractionCoordinatePrograms
public import LogicLineages.PermittedControl.NakedDeltaProgramTargets
@[expose] public section
namespace LogicLineages.PermittedControl.NakedDeltaProgramsProof
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax
open StandardControlCurrent

abbrev Input := Nat × Nat × List Nat × List (List Nat)

theorem result (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun x : Input => NakedDeltaProgram.resultCode p x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  have hc : Computable (fun x : Input × Option (List Nat) × Nat =>
      NakedDeltaProgram.coordinateCode p x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2.2) :=
    Computable.comp
      (f := fun q : PolicyAbstractionCoordinatePrograms.Input =>
        NakedDeltaProgram.coordinateCode p q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
      (g := fun x : Input × Option (List Nat) × Nat =>
        (x.1.1,x.1.2.1,x.1.2.2.1,x.1.2.2.2,x.2.2))
      (PolicyAbstractionCoordinatePrograms.delta p hp)
      ((Computable.fst.comp Computable.fst).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
          ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair
            ((Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair
              (Computable.snd.comp Computable.snd)))))
  have hs : Computable (fun x : Input × Option (List Nat) × Nat => do
      let xs ← x.2.1
      let v ← NakedDeltaProgram.coordinateCode p x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2.2
      pure (xs++[v])) :=
    PolicyPartialMergePrograms.bindTwo (Computable.fst.comp Computable.snd) hc
      (Computable.option_some.comp (Primrec.list_concat.to_comp.comp
        (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)))
  exact ComputableFoldProof.listFold Input Nat (Option (List Nat))
    (fun x => List.range (max (x.1+1) x.2.1+1)) (fun _ => some [])
    (fun x acc j => do
      let xs ← acc
      let v ← NakedDeltaProgram.coordinateCode p x.1 x.2.1 x.2.2.1 x.2.2.2 j
      pure (xs++[v]))
    (Primrec.list_range.to_comp.comp (Computable.succ.comp
      (Primrec.nat_max.to_comp.comp (Computable.succ.comp Computable.fst)
        (Computable.fst.comp Computable.snd)))) (Computable.const (some [])) hs

theorem abstraction (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun x : Nat × Nat × List Nat => NakedDeltaProgram.deltaCode p x.1 x.2.1 x.2.2) := by
  have hr : Computable (fun x : (Nat × Nat × List Nat) × List (List Nat) =>
      NakedDeltaProgram.resultCode p x.1.1 x.1.2.1 x.1.2.2 x.2) :=
    Computable.comp
      (f := fun q : Input => NakedDeltaProgram.resultCode p q.1 q.2.1 q.2.2.1 q.2.2.2)
      (g := fun x : (Nat × Nat × List Nat) × List (List Nat) => (x.1.1,x.1.2.1,x.1.2.2,x.2))
      (result p hp)
      ((Computable.fst.comp Computable.fst).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
          ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair Computable.snd)))
  exact Computable.option_bind (PolicyAbstractionBasePrograms.partials p hp) hr.to₂

theorem programs : NakedDeltaProgramTargets.Programs := by
  intro p hp
  exact ⟨PolicyAbstractionCoordinatePrograms.delta p hp,result p hp,abstraction p hp⟩
end LogicLineages.PermittedControl.NakedDeltaProgramsProof
