module
public import LogicLineages.StandardControlCurrent.PolicyIndexedAbstractionPartialsTargets

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedAbstractionBody
open OrdinalComparison.Source.AdmissibleSum (Policy)
open OrdinalComparison.Source.OrdinalSyntax (node headClosure)
open Nat.Partrec (Code)
open PolicyIndexedAbstractionPartials (Args PartialBackend ImplementsPartial)

abbrev BodyArgs := Args × List (List Nat)

noncomputable def scalarRepeat (c : Code) (count term : Nat) : Part (Option Nat) :=
  if count = 0 then Part.some (some 0) else
    PolicyIndexedShape.macroCode
      (c,PolicyShape.siteCode .scalarRepeat,count-1,List.replicate count term)

noncomputable def delta (b : BodyArgs) (j : Nat) : Part (Option Nat) :=
  let a := b.1
  if j = 0 then scalarRepeat a.1 (PolicyAbstraction.factorCode a.2.1 a.2.2.2)
    ((b.2.getD 0 []).getD 0 0)
  else if j < a.2.1 + 2 then PolicyIndexedShape.macroCode
    (a.1,PolicyShape.siteCode .positiveAbstraction,a.2.2.1,b.2.map (fun xs => xs.getD j 0))
  else Part.some (some (headClosure (a.2.2.2.getD j 0)))

def finish (b : BodyArgs) (j d : Nat) : Nat :=
  if j < b.1.2.2.1 + 1 then node 4 d (headClosure (b.1.2.2.2.getD j 0)) else d

noncomputable def coordinate (b : BodyArgs) (j : Nat) : Part (Option Nat) :=
  (delta b j).map (Option.map (finish b j))

noncomputable def appendCoordinate (b : BodyArgs) (j : Nat) (out : Option (List Nat)) :
    Part (Option (List Nat)) :=
  match out with
  | none => Part.some none
  | some xs => (coordinate b j).map (Option.map (fun x => xs ++ [x]))

noncomputable def prefixCode (b : BodyArgs) (n : Nat) : Part (Option (List Nat)) :=
  n.rec (Part.some (some [])) fun j ih => ih.bind (appendCoordinate b j)

noncomputable def resultCode (b : BodyArgs) : Part (Option (List Nat)) :=
  prefixCode b (max (b.1.2.1 + 1) b.1.2.2.1 + 1)

noncomputable def abstractionCode (run : PartialBackend) (a : Args) : Part (Option (List Nat)) :=
  (PolicyIndexedAbstractionPartials.partialsCode run a).bind fun
    | none => Part.some none
    | some ps => resultCode (a,ps)

def ExactResult : Prop :=
  ∀ (c : Code) (p : Policy), PolicyIndexedShape.Implements c p →
    ∀ level m h ps,
      resultCode ((c,level,m,h),ps) = Part.some (PolicyAbstraction.resultCode p level m h ps)

def ExactAbstraction : Prop :=
  ∀ (run : PartialBackend) (c : Code) (p : Policy),
    PolicyIndexedShape.Implements c p → ImplementsPartial run c p →
    ∀ level m h,
      abstractionCode run (c,level,m,h) = Part.some (PolicyAbstraction.abstractionCode p level m h)

def IndexedAbstractionPartrec : Prop :=
  ∀ (run : PartialBackend), Partrec run → Partrec (abstractionCode run)

end LogicLineages.StandardControlCurrent.PolicyIndexedAbstractionBody
