module
public import LogicLineages.StandardControlCurrent.PolicyIndexedAbstractionBodyTargets
import LogicLineages.StandardControlCurrent.PolicyIndexedAbstractionPartialsProof
import LogicLineages.StandardControlCurrent.PolicyIndexedShapeProof
import LogicLineages.StandardControlCurrent.PolicyAbstractionCoordinatePrograms

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedAbstractionBody
open OrdinalComparison.Source.OrdinalSyntax (headClosure)
open PolicyIndexedShape (exactPolicyIndexedShape policyIndexedShapePartrec MacroArgs)
open PolicyIndexedAbstractionPartials (Args PartialBackend exactPartials indexedPartialsPartrec)

private theorem coordinateExact (c p) (hc : PolicyIndexedShape.Implements c p)
    (level m : Nat) (h : List Nat) (ps : List (List Nat)) (j : Nat) :
    coordinate ((c,level,m,h),ps) j = Part.some (PolicyAbstraction.coordinateCode p level m h ps j) := by
  let d := if j = 0 then PolicyShape.repeatCode p (PolicyShape.siteCode .scalarRepeat)
      (PolicyAbstraction.factorCode level h) ((ps.getD 0 []).getD 0 0)
    else if j < level + 2 then PolicyShape.macroCode p (PolicyShape.siteCode .positiveAbstraction) m
      (ps.map (fun xs => xs.getD j 0))
    else some (headClosure (h.getD j 0))
  have hd : delta ((c,level,m,h),ps) j = Part.some d := by
    change (if j = 0 then scalarRepeat c (PolicyAbstraction.factorCode level h)
        ((ps.getD 0 []).getD 0 0)
      else if j < level + 2 then PolicyIndexedShape.macroCode
        (c,PolicyShape.siteCode .positiveAbstraction,m,ps.map (fun xs => xs.getD j 0))
      else Part.some (some (headClosure (h.getD j 0)))) = Part.some d
    by_cases hz : j = 0
    · by_cases ht : PolicyAbstraction.factorCode level h = 0
      · simp only [d,hz,if_true,scalarRepeat,PolicyShape.repeatCode,ht]
      · simpa only [d,hz,if_true,if_neg ht,scalarRepeat,PolicyShape.repeatCode] using
          exactPolicyIndexedShape c p hc (PolicyShape.siteCode .scalarRepeat)
            (PolicyAbstraction.factorCode level h - 1)
            (List.replicate (PolicyAbstraction.factorCode level h) ((ps.getD 0 []).getD 0 0))
    · by_cases hl : j < level + 2
      · simpa only [d,if_neg hz,if_pos hl] using
          exactPolicyIndexedShape c p hc (PolicyShape.siteCode .positiveAbstraction) m
            (ps.map (fun xs => xs.getD j 0))
      · simp only [d,if_neg hz,if_neg hl]
  unfold coordinate
  rw [hd,Part.map_some]
  have hsource : PolicyAbstraction.coordinateCode p level m h ps j =
      d.bind (fun v => some (finish ((c,level,m,h),ps) j v)) := by
    by_cases hz : j = 0 <;> by_cases hl : j < level + 2 <;>
      simp only [PolicyAbstraction.coordinateCode,d,finish,hz,hl,if_true,if_false,bind,pure]
  rw [hsource]
  cases d <;> rfl

theorem resultExact : ExactResult := by
  intro c p hc level m h ps
  let b : BodyArgs := ((c,level,m,h),ps)
  let step (xs : Option (List Nat)) (j : Nat) : Option (List Nat) := do
    let acc ← xs
    let v ← PolicyAbstraction.coordinateCode p level m h ps j
    pure (acc ++ [v])
  have he (k : Nat) : prefixCode b k = Part.some ((List.range k).foldl step (some [])) := by
    induction k with
    | zero => rfl
    | succ j ih =>
      change ((prefixCode b j).bind (appendCoordinate b j)) = _
      rw [ih,Part.bind_some,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
      generalize (List.range j).foldl step (some []) = acc
      cases acc with
      | none => rfl
      | some xs =>
        change (coordinate ((c,level,m,h),ps) j).map (Option.map (fun v => xs ++ [v])) = _
        rw [coordinateExact c p hc,Part.map_some]
        change Part.some ((PolicyAbstraction.coordinateCode p level m h ps j).map
          (fun x => xs ++ [x])) = Part.some
            ((PolicyAbstraction.coordinateCode p level m h ps j).bind (fun x => some (xs ++ [x])))
        cases PolicyAbstraction.coordinateCode p level m h ps j <;> rfl
  exact he (max (level+1) m+1)

theorem abstractionExact : ExactAbstraction := by
  intro run c p hp hr level m h
  unfold abstractionCode PolicyAbstraction.abstractionCode
  rw [exactPartials run c p hr,Part.bind_some]
  cases PolicyAbstraction.partialsCode p level m h with
  | none => rfl
  | some ps => exact resultExact c p hp level m h ps

private theorem onSome {A B C : Type} [Primcodable A] [Primcodable B] [Inhabited B] [Primcodable C]
    {branch : A → B → Part (Option C)} {fallback : A → Option C}
    (h : Partrec₂ branch) (hfallback : Computable fallback) :
    Partrec (fun x : A × Option B => match x.2 with
      | none => Part.some (fallback x.1)
      | some b => branch x.1 b) := by
  let flag (x : A × Option B) := bif x.2.isSome then 1 else 0
  have hf : Computable flag := Computable.cond
    (Primrec.option_isSome.to_comp.comp Computable.snd) (Computable.const 1) (Computable.const 0)
  have hd : Computable (fun x : A × Option B => x.2.getD default) :=
    Computable.option_getD Computable.snd (Computable.const default)
  have hk : Partrec₂ (fun (x : A × Option B) (_ : Nat) =>
      branch x.1 (x.2.getD default)) :=
    (h.comp (Computable.fst.comp Computable.fst) (hd.comp Computable.fst)).to₂
  exact (Partrec.nat_casesOn_right hf (hfallback.comp Computable.fst) hk).of_eq
    (fun ⟨a,b⟩ => by cases b <;> rfl)

open PolicyAbstractionCoordinatePrograms (Input headP columnP finishP)
private abbrev Q := BodyArgs × Nat

private def flatten (q : Q) : Input := (q.1.1.2.1,q.1.1.2.2.1,q.1.1.2.2.2,q.1.2,q.2)

private theorem flatPR : Primrec flatten := by
  have ha : Primrec (fun q : Q => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hm : Primrec (fun q : Q => q.1.1.2.2) := Primrec.snd.comp ha
  exact (Primrec.fst.comp ha).pair
    ((Primrec.fst.comp hm).pair ((Primrec.snd.comp hm).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))

private theorem indexPR : Primrec (fun q : Q => q.1.1.1) :=
  Primrec.fst.comp (Primrec.fst.comp Primrec.fst)

private def factor (q : Q) : Nat := PolicyAbstraction.factorCode q.1.1.2.1 q.1.1.2.2.2

private def factorArgs (q : Q) : Nat × List Nat := (q.1.1.2.1,q.1.1.2.2.2)

private theorem factorArgsPR : Primrec factorArgs := by
  have fields : Primrec (fun q : Q => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  exact (Primrec.fst.comp fields).pair (Primrec.snd.comp (Primrec.snd.comp fields))

private theorem factorEquation (q : Q) :
    PolicyAbstraction.factorCode (factorArgs q).1 (factorArgs q).2 = factor q := rfl

private theorem factorPR : Primrec factor := by
  let A := Nat × List Nat
  have f : Primrec (fun x : A => PolicyAbstraction.factorCode x.1 x.2) :=
    PolicyAbstractionBasePrograms.factor
  exact (f.comp factorArgsPR).of_eq factorEquation

private def term (q : Q) : Nat := (q.1.2.getD 0 []).getD 0 0

private theorem termPR : Primrec term :=
  (Primrec.list_getD 0).comp
    ((Primrec.list_getD []).comp (Primrec.snd.comp Primrec.fst) (Primrec.const 0)) (Primrec.const 0)

private def scalarRequest (q : Q) : MacroArgs :=
  (q.1.1.1,PolicyShape.siteCode .scalarRepeat,factor q - 1,List.replicate (factor q) (term q))

private theorem scalarRequestPR : Primrec scalarRequest := by
  have replicate : Primrec (fun q : Q => List.replicate (factor q) (term q)) :=
    (Primrec.list_map (Primrec.list_range.comp factorPR)
      (termPR.comp Primrec.fst).to₂).of_eq (fun _ => by simp)
  exact indexPR.pair ((Primrec.const (PolicyShape.siteCode .scalarRepeat)).pair
    ((Primrec.nat_sub.comp factorPR (Primrec.const 1)).pair replicate))

private def positiveRequest (q : Q) : MacroArgs :=
  (q.1.1.1,PolicyShape.siteCode .positiveAbstraction,q.1.1.2.2.1,q.1.2.map (fun xs => xs.getD q.2 0))

private def positiveFields (q : Q) : MacroArgs :=
  (q.1.1.1,PolicyAbstractionCoordinatePrograms.positiveInput (flatten q))

private theorem positiveFieldsPR : Primrec positiveFields := by
  have fields : Primrec (fun q : Q => PolicyAbstractionCoordinatePrograms.positiveInput (flatten q)) :=
    PolicyAbstractionCoordinatePrograms.positiveInputProgram.comp flatPR
  exact indexPR.pair fields

private theorem positiveEquation (q : Q) : positiveFields q = positiveRequest q := rfl

private theorem positiveRequestPR : Primrec positiveRequest :=
  positiveFieldsPR.of_eq positiveEquation

private def request (q : Q) : Option MacroArgs :=
  if q.2 = 0 then (if factor q = 0 then none else some (scalarRequest q))
  else if q.2 < q.1.1.2.1 + 2 then some (positiveRequest q) else none

private def head (q : Q) : Nat := headClosure (q.1.1.2.2.2.getD q.2 0)

private theorem headEquation (q : Q) :
    headClosure ((flatten q).2.2.1.getD (flatten q).2.2.2.2 0) = head q := rfl

private theorem headPR : Primrec head :=
  (headP.comp flatPR).of_eq headEquation

private def fallback (q : Q) : Option Nat :=
  if q.2 = 0 then some 0 else some (headClosure (q.1.1.2.2.2.getD q.2 0))

private def zeroIndex (q : Q) : Prop := q.2 = 0
private instance (q : Q) : Decidable (zeroIndex q) := inferInstanceAs (Decidable (q.2 = 0))
private theorem zeroIndexPR : PrimrecPred zeroIndex :=
  Primrec.eq.comp Primrec.snd (Primrec.const 0)

private def zeroFactor (q : Q) : Prop := factor q = 0
private instance (q : Q) : Decidable (zeroFactor q) := inferInstanceAs (Decidable (factor q = 0))
private theorem zeroFactorPR : PrimrecPred zeroFactor :=
  Primrec.eq.comp factorPR (Primrec.const 0)

private def insidePositive (q : Q) : Prop := q.2 < q.1.1.2.1 + 2
private instance (q : Q) : Decidable (insidePositive q) :=
  inferInstanceAs (Decidable (q.2 < q.1.1.2.1 + 2))

private theorem levelProjectionPR : Primrec (fun q : Q => q.1.1.2.1) := by
  have fields : Primrec (fun q : Q => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  exact Primrec.fst.comp fields

private theorem thresholdPR : Primrec (fun q : Q => q.1.1.2.1 + 2) :=
  Primrec.nat_add.comp levelProjectionPR (Primrec.const 2)

private theorem insidePositivePR : PrimrecPred insidePositive :=
  Primrec.nat_lt.comp Primrec.snd thresholdPR

private def zeroRequest (q : Q) : Option MacroArgs :=
  if zeroFactor q then none else some (scalarRequest q)

private def aboveZeroRequest (q : Q) : Option MacroArgs :=
  if insidePositive q then some (positiveRequest q) else none

private theorem requestEquation (q : Q) :
    (if zeroIndex q then zeroRequest q else aboveZeroRequest q) = request q := rfl

private theorem fallbackEquation (q : Q) :
    (if zeroIndex q then some 0 else some (head q)) = fallback q := rfl

attribute [local irreducible] factorArgs positiveFields scalarRequest positiveRequest
  factor head zeroIndex zeroFactor insidePositive

private theorem zeroRequestPR : Primrec zeroRequest :=
  Primrec.ite zeroFactorPR (Primrec.const (none : Option MacroArgs))
    (Primrec.option_some.comp scalarRequestPR)

private theorem aboveZeroRequestPR : Primrec aboveZeroRequest :=
  Primrec.ite insidePositivePR (Primrec.option_some.comp positiveRequestPR)
    (Primrec.const (none : Option MacroArgs))

attribute [local irreducible] zeroRequest aboveZeroRequest

private theorem requestPR : Primrec request :=
  (Primrec.ite zeroIndexPR zeroRequestPR aboveZeroRequestPR).of_eq requestEquation

private theorem fallbackPR : Primrec fallback := by
  have tail : Primrec (fun q : Q => some (head q)) := Primrec.option_some.comp headPR
  exact (Primrec.ite zeroIndexPR (Primrec.const (some 0)) tail).of_eq fallbackEquation

private theorem deltaEquation (q : Q) :
    (match request q with
    | none => Part.some (fallback q)
    | some req => PolicyIndexedShape.macroCode req) = delta q.1 q.2 := by
  by_cases hz : q.2 = 0
  · by_cases ht : PolicyAbstraction.factorCode q.1.1.2.1 q.1.1.2.2.2 = 0 <;>
      simp [request,fallback,delta,scalarRepeat,scalarRequest,factor,term,hz,ht]
  · by_cases ht : q.2 < q.1.1.2.1 + 2 <;>
      simp [request,fallback,delta,positiveRequest,hz,ht]

private def finishArgs (q : Q × Nat) : Input × Nat := (flatten q.1,q.2)

private theorem finishArgsPR : Primrec finishArgs :=
  (flatPR.comp Primrec.fst).pair Primrec.snd

private theorem finishEquation (q : Q × Nat) :
    (if (finishArgs q).1.2.2.2.2 < (finishArgs q).1.2.1 + 1 then
        OrdinalComparison.Source.OrdinalSyntax.node 4 (finishArgs q).2
          (headClosure ((finishArgs q).1.2.2.1.getD (finishArgs q).1.2.2.2.2 0))
      else (finishArgs q).2) = finish q.1.1 q.1.2 q.2 := rfl

private theorem finishPR : Primrec (fun q : Q × Nat => finish q.1.1 q.1.2 q.2) :=
  (finishP.comp finishArgsPR).of_eq finishEquation

private theorem coordinateEquation (q : Q) :
    (delta q.1 q.2).map (Option.map (finish q.1 q.2)) = coordinate q.1 q.2 := rfl

private theorem appendEquation (q : Q × Option (List Nat)) :
    (match q.2 with
    | none => Part.some none
    | some xs => (coordinate q.1.1 q.1.2).map (Option.map (fun v => xs ++ [v]))) =
      appendCoordinate q.1.1 q.1.2 q.2 := rfl

private theorem prefixEquation (q : Q) :
    q.2.rec (Part.some (some [])) (fun j ih => ih.bind (appendCoordinate q.1 j)) =
      prefixCode q.1 q.2 := rfl

private theorem resultEquation (b : BodyArgs) :
    prefixCode b (max (b.1.2.1 + 1) b.1.2.2.1 + 1) = resultCode b := rfl

private theorem abstractionEquation (run : PartialBackend) (q : Args) :
    (PolicyIndexedAbstractionPartials.partialsCode run q).bind (fun o => match o with
    | none => Part.some none
    | some ps => resultCode (q,ps)) = abstractionCode run q := rfl

attribute [local irreducible] PolicyIndexedShape.macroCode request fallback delta finish
  coordinate appendCoordinate prefixCode resultCode abstractionCode

private theorem deltaPartrec : Partrec (fun q : Q => delta q.1 q.2) := by
  have hm : Partrec₂ (fun (_ : Q) (req : MacroArgs) => PolicyIndexedShape.macroCode req) :=
    (policyIndexedShapePartrec.comp Computable.snd).to₂
  have h := (onSome hm fallbackPR.to_comp).comp (Computable.id.pair requestPR.to_comp)
  apply h.of_eq
  intro q
  rw [← deltaEquation q]
  cases request q <;> rfl

private theorem coordinatePartrec : Partrec (fun q : Q => coordinate q.1 q.2) := by
  have hf : Computable₂ (fun (q : Q) (o : Option Nat) => o.map (finish q.1 q.2)) := by
    let P := Q × Option Nat
    have hg : Computable₂ (fun (q : P) (v : Nat) => finish q.1.1 q.1.2 v) :=
      (finishPR.to_comp.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)).to₂
    exact (Computable.option_map (Computable.snd : Computable (fun q : P => q.2)) hg).to₂
  exact (deltaPartrec.map hf).of_eq coordinateEquation

private theorem appendPartrec :
    Partrec (fun q : Q × Option (List Nat) => appendCoordinate q.1.1 q.1.2 q.2) := by
  let P := Q × List Nat
  have hc : Partrec (fun q : P => coordinate q.1.1 q.1.2) :=
    coordinatePartrec.comp Computable.fst
  have hf : Computable₂ (fun (q : P) (o : Option Nat) => o.map (fun v => q.2 ++ [v])) := by
    let R := P × Option Nat
    have h : Computable₂ (fun (q : R) (v : Nat) => q.1.2 ++ [v]) :=
      (Primrec.list_concat.to_comp.comp
        (Computable.snd.comp (Computable.fst.comp Computable.fst)) Computable.snd).to₂
    exact (Computable.option_map (Computable.snd : Computable (fun q : R => q.2)) h).to₂
  have h := onSome (hc.map hf).to₂ (Computable.const none)
  apply h.of_eq
  intro q
  rw [← appendEquation q]
  rcases q with ⟨b,o⟩
  cases o <;> rfl

private theorem prefixPartrec : Partrec (fun q : Q => prefixCode q.1 q.2) := by
  let P := Q × Nat × Option (List Nat)
  have h : Computable (fun q : P => ((q.1.1,q.2.1),q.2.2)) :=
    ((Computable.fst.comp Computable.fst).pair (Computable.fst.comp Computable.snd)).pair
      (Computable.snd.comp Computable.snd)
  have start : Computable (fun _ : Q => (some [] : Option (List Nat))) := Computable.const _
  exact (Partrec.nat_rec Computable.snd start (appendPartrec.comp h).to₂).of_eq prefixEquation

private theorem resultPartrec : Partrec resultCode := by
  have ha : Primrec (fun b : BodyArgs => b.1.2) := Primrec.snd.comp Primrec.fst
  have hm : Primrec (fun b : BodyArgs => b.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp ha)
  have hn : Computable (fun b : BodyArgs => max (b.1.2.1+1) b.1.2.2.1+1) :=
    (Primrec.succ.comp (Primrec.nat_max.comp (Primrec.succ.comp (Primrec.fst.comp ha)) hm)).to_comp
  exact (prefixPartrec.comp (Computable.id.pair hn)).of_eq resultEquation

theorem abstractionPartrec : IndexedAbstractionPartrec := by
  intro run hr
  have branch : Partrec₂ (fun (a : Args) (ps : List (List Nat)) => resultCode (a,ps)) :=
    resultPartrec.to₂
  have h := onSome branch (Computable.const none)
  apply ((indexedPartialsPartrec run hr).bind h.to₂).of_eq
  intro q
  rw [← abstractionEquation run q]
  apply congrArg (fun f : Option (List (List Nat)) → Part (Option (List Nat)) =>
    (PolicyIndexedAbstractionPartials.partialsCode run q).bind f)
  funext o
  cases o <;> rfl

end LogicLineages.StandardControlCurrent.PolicyIndexedAbstractionBody
