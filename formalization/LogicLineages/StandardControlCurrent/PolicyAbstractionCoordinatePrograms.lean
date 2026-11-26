module
public import LogicLineages.StandardControlCurrent.PolicyAbstractionBasePrograms
public import LogicLineages.StandardControlCurrent.PolicyShapeProgramsProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyAbstractionCoordinatePrograms
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax

abbrev Input := Nat × Nat × List Nat × List (List Nat) × Nat

theorem levelP : Primrec (fun x : Input => x.1) := Primrec.fst
theorem mP : Primrec (fun x : Input => x.2.1) := Primrec.fst.comp Primrec.snd
theorem hP : Primrec (fun x : Input => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem psP : Primrec (fun x : Input => x.2.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem jP : Primrec (fun x : Input => x.2.2.2.2) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

theorem headP : Primrec (fun x : Input => headClosure (x.2.2.1.getD x.2.2.2.2 0)) :=
  ordinalSyntaxHeadOperationsPrimitiveRecursive.2.1.comp ((Primrec.list_getD 0).comp hP jP)

theorem columnP : Primrec (fun x : Input => x.2.2.2.1.map (fun xs => xs.getD x.2.2.2.2 0)) :=
  Primrec.list_map psP ((Primrec.list_getD 0).comp Primrec.snd (jP.comp Primrec.fst)).to₂

attribute [local irreducible] PolicyShape.macroCode PolicyShape.repeatCode

theorem scalar (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun x : Input => PolicyShape.repeatCode p (PolicyShape.siteCode .scalarRepeat)
      (PolicyAbstraction.factorCode x.1 x.2.2.1) ((x.2.2.2.1.getD 0 []).getD 0 0)) :=
  Computable.comp (f := fun q : Nat × Nat × Nat => PolicyShape.repeatCode p q.1 q.2.1 q.2.2)
    (g := fun x : Input => (PolicyShape.siteCode .scalarRepeat,PolicyAbstraction.factorCode x.1 x.2.2.1,
      (x.2.2.2.1.getD 0 []).getD 0 0)) (PolicyShapeProgramsProof.policies p hp).2
    ((Computable.const (PolicyShape.siteCode .scalarRepeat)).pair
      ((PolicyAbstractionBasePrograms.factor.to_comp.comp (levelP.to_comp.pair hP.to_comp)).pair
        ((Primrec.list_getD 0).to_comp.comp
          ((Primrec.list_getD []).to_comp.comp psP.to_comp (Computable.const 0)) (Computable.const 0))))

def positiveInput (x : Input) : Nat × Nat × List Nat :=
  (PolicyShape.siteCode .positiveAbstraction,x.2.1,
    x.2.2.2.1.map (fun xs => xs.getD x.2.2.2.2 0))

theorem positiveInputProgram : Primrec positiveInput :=
  (Primrec.const (PolicyShape.siteCode .positiveAbstraction)).pair (mP.pair columnP)

attribute [local irreducible] positiveInput

theorem positiveComposition (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun x : Input => PolicyShape.macroCode p (positiveInput x).1
      (positiveInput x).2.1 (positiveInput x).2.2) := by
  have hm : Computable (fun q : Nat × Nat × List Nat => PolicyShape.macroCode p q.1 q.2.1 q.2.2) :=
    (PolicyShapeProgramsProof.policies p hp).1
  exact Computable.comp (f := fun q : Nat × Nat × List Nat => PolicyShape.macroCode p q.1 q.2.1 q.2.2)
    (g := positiveInput) hm positiveInputProgram.to_comp

theorem positive (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun x : Input => PolicyShape.macroCode p (PolicyShape.siteCode .positiveAbstraction)
      x.2.1 (x.2.2.2.1.map (fun xs => xs.getD x.2.2.2.2 0))) :=
  (positiveComposition p hp).of_eq (fun x => by unfold positiveInput; rfl)

theorem choose {α β : Type} [Primcodable α] [Primcodable β]
    {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : PrimrecPred p) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) :=
  (Computable.cond hp.decide.to_comp hf hg).of_eq (fun a => by simp)

theorem delta (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun x : Input => if x.2.2.2.2=0 then
      PolicyShape.repeatCode p (PolicyShape.siteCode .scalarRepeat)
        (PolicyAbstraction.factorCode x.1 x.2.2.1) ((x.2.2.2.1.getD 0 []).getD 0 0)
      else if x.2.2.2.2<x.1+2 then
        PolicyShape.macroCode p (PolicyShape.siteCode .positiveAbstraction) x.2.1
          (x.2.2.2.1.map (fun xs => xs.getD x.2.2.2.2 0))
      else some (headClosure (x.2.2.1.getD x.2.2.2.2 0))) :=
  choose (Primrec.eq.comp jP (Primrec.const 0)) (scalar p hp)
    (choose (Primrec.nat_lt.comp jP (Primrec.nat_add.comp levelP (Primrec.const 2)))
      (positive p hp) (Computable.option_some.comp headP.to_comp))

theorem finishP : Primrec (fun x : Input × Nat =>
    if x.1.2.2.2.2<x.1.2.1+1 then node 4 x.2 (headClosure (x.1.2.2.1.getD x.1.2.2.2.2 0)) else x.2) :=
  Primrec.ite ((Primrec.nat_lt.comp jP (Primrec.succ.comp mP)).comp Primrec.fst)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
      (Primrec₂.natPair.comp Primrec.snd (headP.comp Primrec.fst))) (Primrec.const 4)) Primrec.snd

theorem coordinate (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun x : Input => PolicyAbstraction.coordinateCode p x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  have h := Computable.option_map (delta p hp) finishP.to_comp.to₂
  apply h.of_eq
  intro x
  unfold PolicyAbstraction.coordinateCode
  by_cases hz : x.2.2.2.2=0 <;> by_cases hl : x.2.2.2.2<x.1+2 <;>
    simp only [hz,hl,if_true,if_false,Option.map_eq_bind,bind,pure,Function.comp_def]
end LogicLineages.StandardControlCurrent.PolicyAbstractionCoordinatePrograms
