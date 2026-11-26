module

public import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms

public section
namespace LogicLineages.PersistentMarking.NumberedWindowPositivePathWalkPrograms
open NumberedWindowPositivePathAlgorithm NumberedWindowPositivePathProgramTargets
open NumberedWindowPositivePathParserPrograms
open NumberedWindowSyntaxShapePrograms (anyOption)

private abbrev Scope := List Nat × Nat
private abbrev Config := Scope × Option Nat × Nat

private def checkHop (step : Step) (least : Least) (scope : Scope) (source : Nat) (hop : ClassHop) :
    Option Nat :=
  let (ctx,ty) := scope
  let (target,q,w,r) := hop
  if step ctx ty q w r && (least ctx ty q == some source) && (least ctx ty r == some target) then
    some target
  else none

private theorem checkHopPrim {step : Step} {least : Least}
    (hs : Primrec (fun p : StepInput => step p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (hl : Primrec (fun p : LeastInput => least p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Scope × Nat × ClassHop => checkHop step least p.1 p.2.1 p.2.2) := by
  let E := Scope × Nat × ClassHop
  have ctx : Primrec (fun p : E => p.1.1) := Primrec.fst.comp Primrec.fst
  have ty : Primrec (fun p : E => p.1.2) := Primrec.snd.comp Primrec.fst
  have src : Primrec (fun p : E => p.2.1) := Primrec.fst.comp Primrec.snd
  have hop : Primrec (fun p : E => p.2.2) := Primrec.snd.comp Primrec.snd
  have dst := Primrec.option_some.comp (Primrec.fst.comp hop)
  have q := Primrec.fst.comp (Primrec.snd.comp hop)
  have w := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hop))
  have r := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hop))
  have raw := hs.comp (ctx.pair (ty.pair (q.pair (w.pair r))))
  have srcLeast := equalPrim.comp (hl.comp (ctx.pair (ty.pair q))) (Primrec.option_some.comp src)
  have dstLeast := equalPrim.comp (hl.comp (ctx.pair (ty.pair r))) dst
  exact Primrec.ite (Primrec.eq.comp (Primrec.and.comp (Primrec.and.comp raw srcLeast) dstLeast)
    (Primrec.const true)) dst (Primrec.const none)

private theorem advancePrim {step : Step} {least : Least}
    (hs : Primrec (fun p : StepInput => step p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (hl : Primrec (fun p : LeastInput => least p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Config => advance (step p.1.1 p.1.2) (least p.1.1 p.1.2) p.2.1 p.2.2) := by
  have code : Primrec (fun p : Config × Nat => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have scope : Primrec (fun p : (Config × Nat) × ClassHop => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have cur : Primrec (fun p : (Config × Nat) × ClassHop => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have check := (checkHopPrim hs hl).comp (scope.pair (cur.pair Primrec.snd))
  exact Primrec.option_bind (Primrec.fst.comp Primrec.snd)
    (Primrec.option_bind (hopPrim.comp code) check.to₂).to₂

theorem positivePrim {step : Step} {least : Least}
    (hs : Primrec (fun p : StepInput => step p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (hl : Primrec (fun p : LeastInput => least p.1 p.2.1 p.2.2)) :
    Primrec (fun p : PathInput => positive step least p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let Data := PathInput × List Nat
  have scope : Primrec (fun p : Data × Option Nat × Nat => (p.1.1.1,p.1.1.2.1)) :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have src : Primrec (fun p : Data => p.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have dst : Primrec (fun p : Data => p.1.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have cert : Primrec (fun p : PathInput => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have fold := Primrec.list_foldl (Primrec.snd : Primrec (Prod.snd : Data → List Nat))
    (Primrec.option_some.comp src) ((advancePrim hs hl).comp (scope.pair Primrec.snd)).to₂
  have final := equalPrim.comp fold (Primrec.option_some.comp dst)
  have nonempty : Primrec (fun p : Data => !p.2.isEmpty) :=
    ((Primrec.eq.comp Primrec.snd (Primrec.const ([] : List Nat))).not.decide).of_eq
      (fun p => by cases p.2 <;> simp)
  exact anyOption (fieldsPrim.comp cert) (Primrec.and.comp nonempty final).to₂

end LogicLineages.PersistentMarking.NumberedWindowPositivePathWalkPrograms
