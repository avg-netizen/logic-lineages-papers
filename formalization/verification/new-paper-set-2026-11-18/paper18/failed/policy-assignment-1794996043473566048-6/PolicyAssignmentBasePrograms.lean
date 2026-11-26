module
public import LogicLineages.StandardControlCurrent.PolicyAssignmentTargets
public import LogicLineages.StandardControlCurrent.PolicyConstructorsProgramsProof
public import LogicLineages.StandardControlCurrent.PolicyAbstractionProgramsProof
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckStatementChecks
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyAssignmentBasePrograms
open OrdinalComparison Source Source.AdmissibleSum Source.SyntaxCode Source.OrdinalSyntax
open PolicyAbstractionCoordinatePrograms (choose)

theorem variablesP : Primrec (fun x : Nat × Nat × Nat =>
    (List.range (x.2.2+1)).map (fun i => 8*Nat.pair x.2.1 i+3)) := by
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.snd)))
  exact (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
    (Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
    (Primrec.const 3)).to₂

theorem onesP : Primrec (fun x : Nat × Nat × Nat => List.replicate (x.2.2+1) 1) := by
  have h := Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.const 1).to₂
  exact h.of_eq (fun x => by simp)

theorem prime (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun x : Nat × Nat × Nat => PolicyAssignment.primeCode p x.1 x.2.1 x.2.2) := by
  have hr : Computable (fun x : Nat × Nat × Nat =>
      PolicyConstructors.recursorCode p (typeLevel x.2.1) x.2.2) :=
    Computable.comp (f := fun q : Nat × Nat => PolicyConstructors.recursorCode p q.1 q.2)
      (g := fun x : Nat × Nat × Nat => (typeLevel x.2.1,x.2.2))
      ((PolicyConstructorsProgramsProof.programs.2 p hp).1)
      ((SyntaxCode.StatementChecks.typeLevelPrimitiveRecursive.to_comp.comp
        (Computable.fst.comp Computable.snd)).pair (Computable.snd.comp Computable.snd))
  exact choose (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (Computable.option_some.comp variablesP.to_comp)
    (choose (Primrec.eq.comp Primrec.fst (Primrec.const 4)) hr
      (Computable.option_some.comp onesP.to_comp))

theorem appBind (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun x : Nat × Nat × Option (List Nat) × Option (List Nat) =>
      x.2.2.1.bind (fun f => x.2.2.2.bind (fun a => PolicyConstructors.applicationCode p x.1 x.2.1 f a))) := by
  let A := Nat × Nat × Option (List Nat) × Option (List Nat)
  have hf : Computable (fun x : A × List Nat × List Nat =>
      PolicyConstructors.applicationCode p x.1.1 x.1.2.1 x.2.1 x.2.2) :=
    Computable.comp
      (f := fun q : Nat × Nat × List Nat × List Nat => PolicyConstructors.applicationCode p q.1 q.2.1 q.2.2.1 q.2.2.2)
      (g := fun x : A × List Nat × List Nat => (x.1.1,x.1.2.1,x.2.1,x.2.2))
      (PolicyConstructorsProgramsProof.programs.2 p hp).2.2
      ((Computable.fst.comp Computable.fst).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
          ((Computable.fst.comp Computable.snd).pair (Computable.snd.comp Computable.snd))))
  exact PolicyPartialMergePrograms.bindTwo
    (Computable.fst.comp (Computable.snd.comp Computable.snd))
    (Computable.snd.comp (Computable.snd.comp Computable.snd)) hf

theorem lamBind (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun x : Nat × Nat × Option (List Nat) =>
      x.2.2.bind (fun b => PolicyAbstraction.abstractionCode p x.1 x.2.1 b)) := by
  have hb : Computable (fun x : (Nat × Nat × Option (List Nat)) × List Nat =>
      PolicyAbstraction.abstractionCode p x.1.1 x.1.2.1 x.2) :=
    Computable.comp (f := fun q : Nat × Nat × List Nat => PolicyAbstraction.abstractionCode p q.1 q.2.1 q.2.2)
      (g := fun x : (Nat × Nat × Option (List Nat)) × List Nat => (x.1.1,x.1.2.1,x.2))
      (PolicyAbstractionProgramsProof.abstraction p hp)
      ((Computable.fst.comp Computable.fst).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd))
  exact Computable.option_bind (Computable.snd.comp Computable.snd) hb.to₂
end LogicLineages.StandardControlCurrent.PolicyAssignmentBasePrograms
