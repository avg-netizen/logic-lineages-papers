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

private theorem prefixEquation (run : PartialBackend) (q : Args × Nat) :
    q.2.rec (Part.some []) (fun i ih => ih.bind (fun rs =>
      (run (callArgs q.1 i)).map (fun r => rs ++ [r]))) =
    prefixCode run q.1 q.2 := rfl

private theorem partialsEquation (run : PartialBackend) (q : Args) :
    (prefixCode run q (q.2.2.1 + 1)).map collectLists = partialsCode run q := rfl

attribute [local irreducible] callArgs prefixCode partialsCode

private theorem prefixPartrec (run : PartialBackend) (hr : Partrec run) :
    Partrec (fun q : Args × Nat => prefixCode run q.1 q.2) := by
  let Results := List (Option (List Nat))
  let P := (Args × Nat) × Nat × Results
  have arg : Computable (fun q : P => (q.1.1,q.2.1)) :=
    (Computable.fst.comp Computable.fst).pair (Computable.fst.comp Computable.snd)
  have eval : Partrec (fun q : P => run (callArgs q.1.1 q.2.1)) :=
    hr.comp (callArgsPrim.to_comp.comp arg)
  have add : Computable₂ (fun (q : P) (r : Option (List Nat)) => q.2.2 ++ [r]) :=
    (Primrec.list_concat.to_comp.comp
      (Computable.snd.comp (Computable.snd.comp Computable.fst)) Computable.snd).to₂
  have start : Computable (fun _ : Args × Nat => ([] : Results)) := Computable.const []
  have h := Partrec.nat_rec Computable.snd start (eval.map add).to₂
  exact h.of_eq (prefixEquation run)

theorem indexedPartialsPartrec : IndexedPartialsPartrec := by
  intro run hr
  have count : Computable (fun q : Args => q.2.2.1 + 1) :=
    Computable.succ.comp (Computable.fst.comp (Computable.snd.comp Computable.snd))
  have main := (prefixPartrec run hr).comp (Computable.id.pair count)
  have collect : Computable₂ (fun (_ : Args) rs => collectLists rs) :=
    (PolicyAbstractionBasePrograms.collectPrim.to_comp.comp Computable.snd).to₂
  exact (main.map collect).of_eq (partialsEquation run)

end LogicLineages.StandardControlCurrent.PolicyIndexedAbstractionPartials
