module
public import LogicLineages.StandardControlCurrent.PolicyIndexedAbstractionPartialsTargets
import LogicLineages.StandardControlCurrent.PolicyAbstractionBasePrograms

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedAbstractionPartials
open OrdinalComparison.Source.OrdinalSyntax (collectLists)

theorem exactPartials : ExactPartials := by
  intro run c p hc level m h
  let arg : Args := (c,level,m,h)
  let read (i : Nat) : Option (List Nat) := PolicyPartial.run p level i (h.getD i 0)
  have pref (k : Nat) : prefixCode run arg k = Part.some ((List.range k).map read) := by
    induction k with
    | zero => rfl
    | succ i ih =>
      change ((prefixCode run arg i).bind (fun rs =>
        (run (callArgs arg i)).map (fun r => rs ++ [r]))) = _
      rw [ih,Part.bind_some]
      change (run (c,level,i,h.getD i 0)).map _ = _
      rw [hc,Part.map_some,List.range_succ,List.map_append,List.map_cons,List.map_nil] <;> rfl
  change (prefixCode run arg (m+1)).map collectLists =
    Part.some (collectLists ((List.range (m+1)).map read))
  rw [pref,Part.map_some]

private theorem callArgsPrim : Primrec (fun q : Args × Nat => callArgs q.1 q.2) := by
  have hctx : Primrec (fun q : Args × Nat => q.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hbody : Primrec (fun q : Args × Nat => q.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp hctx)
  exact (Primrec.fst.comp Primrec.fst).pair
    ((Primrec.fst.comp hctx).pair
      (Primrec.snd.pair ((Primrec.list_getD 0).comp hbody Primrec.snd)))

private theorem partialsEquation (run : PartialBackend) (q : Args) :
    (prefixCode run q (q.2.2.1 + 1)).map collectLists = partialsCode run q := rfl

private abbrev Results := List (Option (List Nat))
private abbrev Input := Args × Nat
private abbrev Step := Input × (Nat × Results)
private abbrev Finished := Step × Option (List Nat)

private def stepArg (q : Step) : Args × Nat := (q.1.1,q.2.1)

private def stepAppend (q : Finished) : Results := q.1.2.2 ++ [q.2]

private noncomputable def advance (run : PartialBackend) (q : Step) : Part Results :=
  (run (callArgs (stepArg q).1 (stepArg q).2)).map (fun r => stepAppend (q,r))

private theorem stepArgProgram : Computable stepArg :=
  (Computable.fst.comp Computable.fst).pair (Computable.fst.comp Computable.snd)

private theorem stepAppendProgram : Computable stepAppend :=
  Primrec.list_concat.to_comp.comp
    (Computable.snd.comp (Computable.snd.comp Computable.fst)) Computable.snd

private theorem advanceEquation (run : PartialBackend) (q : Step) :
    (run (callArgs (stepArg q).1 (stepArg q).2)).map (fun r => stepAppend (q,r)) =
      advance run q := rfl

private theorem advancePrefixEquation (run : PartialBackend) (x : Input) :
    x.2.rec (Part.some []) (fun i ih => ih.bind (fun rs => advance run (x,i,rs))) =
      prefixCode run x.1 x.2 := rfl

attribute [local irreducible] callArgs prefixCode partialsCode stepArg stepAppend advance

private theorem advancePartrec (run : PartialBackend) (hr : Partrec run) :
    Partrec (advance run) := by
  have read : Computable (fun q : Step => callArgs (stepArg q).1 (stepArg q).2) :=
    callArgsPrim.to_comp.comp stepArgProgram
  have evaluation : Partrec (fun q : Step => run (callArgs (stepArg q).1 (stepArg q).2)) :=
    hr.comp read
  have program : Computable₂ (fun (q : Step) (r : Option (List Nat)) => stepAppend (q,r)) :=
    stepAppendProgram.to₂
  exact (Partrec.map evaluation program).of_eq (advanceEquation run)

private theorem prefixPartrec (run : PartialBackend) (hr : Partrec run) :
    Partrec (fun q : Input => prefixCode run q.1 q.2) := by
  have count : Computable (fun q : Input => q.2) := Computable.snd
  have start : Computable (fun _ : Input => ([] : Results)) := Computable.const []
  have step : Partrec₂ (fun (q : Input) (s : Nat × Results) => advance run (q,s)) :=
    (advancePartrec run hr).to₂
  exact (Partrec.nat_rec count start step).of_eq (advancePrefixEquation run)

theorem indexedPartialsPartrec : IndexedPartialsPartrec := by
  intro run hr
  have count : Computable (fun q : Args => q.2.2.1 + 1) :=
    Computable.succ.comp (Computable.fst.comp (Computable.snd.comp Computable.snd))
  have main := (prefixPartrec run hr).comp (Computable.id.pair count)
  have collect : Computable₂ (fun (_ : Args) rs => collectLists rs) :=
    (PolicyAbstractionBasePrograms.collectPrim.to_comp.comp Computable.snd).to₂
  exact (main.map collect).of_eq (partialsEquation run)

end LogicLineages.StandardControlCurrent.PolicyIndexedAbstractionPartials
