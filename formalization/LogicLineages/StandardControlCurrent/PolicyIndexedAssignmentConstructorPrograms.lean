module
public import LogicLineages.StandardControlCurrent.PolicyIndexedAssignmentTargets
import LogicLineages.StandardControlCurrent.PolicyIndexedShapeProof
import LogicLineages.OrdinalComparison.WWOrdinalSyntaxBoxComputability
import Mathlib.Computability.RE

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedAssignment
open OrdinalComparison Source Source.OrdinalSyntax
open Nat.Partrec (Code)

theorem partChoose {T Y : Type} [Primcodable T] [Primcodable Y]
    {p : T → Prop} [DecidablePred p] {f g : T → Part Y}
    (hp : PrimrecPred p) (hf : Partrec f) (hg : Partrec g) :
    Partrec (fun x => if p x then f x else g x) :=
  (Partrec.cond hp.decide.to_comp hf hg).of_eq (by intro x; by_cases h : p x <;> simp [h])

/-- Optional data refusal returns an inner none; only the selected actual
backend can diverge. -/
theorem partialOnSome {T X Y : Type} [Primcodable T] [Primcodable X] [Primcodable Y]
    {get : T → Option X} {onSome : T → X → Part (Option Y)}
    (hget : Computable get) (hcall : Partrec₂ onSome) :
    Partrec (fun x => match get x with
      | none => Part.some none
      | some y => onSome x y) := by
  have h := Partrec.bind (Computable.ofOption hget) hcall
  apply (Partrec.cond (Primrec.option_isSome.to_comp.comp hget) h
    (Partrec.const' (Part.some (none : Option Y)))).of_eq
  intro x
  cases e : get x <;> simp [e,Part.bind_some]

theorem partialMapSome {T X Y : Type} [Primcodable T] [Primcodable X] [Primcodable Y]
    {f : T → Part (Option X)} {g : T → X → Y}
    (hf : Partrec f) (hg : Computable₂ g) :
    Partrec (fun p => (f p).map (Option.map (g p))) := by
  let A := T × Option X
  have applyValue : Computable₂ (fun (p : A) (x : X) => g p.1 x) :=
    (hg.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
  exact Partrec.map hf (Computable.option_map Computable.snd applyValue).to₂

private theorem nodePrim {α : Type} [Primcodable α] {t a b : α → Nat}
    (ht : Primrec t) (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => node (t x) (a x) (b x)) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
    (Primrec₂.natPair.comp ha hb)) ht

private theorem recFieldsPrim : Primrec (fun x : Nat × Nat × Nat => recursorFrom x.1 x.2.1 x.2.2) := by
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.ite (Primrec.eq.comp Primrec.snd
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 2)))
      (Primrec.const 2) (Primrec.const 1))

private theorem appFieldsPrim : Primrec (fun x : Nat × Nat × List Nat × List Nat × Nat =>
    applicationFrom x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  let P := Nat × Nat × List Nat × List Nat × Nat
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst))
  have ha : Primrec (fun x : P × Nat => x.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hf : Primrec (fun x : P × Nat => x.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hg : Primrec (fun x : P × Nat => x.1.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have ht : Primrec (fun x : P × Nat => x.1.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have bp {i : P × Nat → Nat} (hi : Primrec i) : Primrec (fun x => boxPositive x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 (i x)) :=
    ordinalSyntaxBoxOperationsPrimitiveRecursive.1.comp (ha.pair (hf.pair (hg.pair hi)))
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (nodePrim (Primrec.const 6) (bp (Primrec.const 1)) ht) (bp Primrec.snd)

theorem numeralPartrec : Partrec₂ numeral := by
  let A := Code × Nat
  have x : Primrec (Prod.snd : A → Nat) := Primrec.snd
  have tape : Primrec (fun p : A => List.replicate p.2 (1 : Nat)) := by
    have h := Primrec.list_map (Primrec.list_range.comp x) (Primrec.const 1).to₂
    exact h.of_eq (by intro p; simp)
  have n : Primrec (fun p : A => p.2-1) := Primrec.nat_sub.comp x (Primrec.const 1)
  have call := PolicyIndexedShape.policyIndexedShapePartrec.comp
    ((Computable.fst : Computable (Prod.fst : A → Code)).pair
      ((Computable.const (PolicyShape.siteCode .numeral)).pair (n.to_comp.pair tape.to_comp)))
  exact (partChoose (Primrec.eq.comp x (Primrec.const 0))
    (Partrec.const' (Part.some (some 0))) call).to₂

theorem tailPartrec : Partrec (fun p : Code × Nat × Nat × Nat =>
    tailCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let A := Code × Nat × Nat × Nat
  have c : Computable (Prod.fst : A → Code) := Computable.fst
  have n : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have f : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have g : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have tape : Primrec (fun p : A × Nat => [p.1.2.2.1,p.1.2.2.2,p.2]) :=
    Primrec.list_cons.comp (f.comp Primrec.fst)
      (Primrec.list_cons.comp (g.comp Primrec.fst)
        (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))
  have expansion : Partrec₂ (fun (p : A) (num : Nat) =>
      PolicyIndexedShape.macroCode (p.1,PolicyShape.siteCode .optionalBoxTail,2,[p.2.2.1,p.2.2.2,num])) :=
    (PolicyIndexedShape.policyIndexedShapePartrec.comp ((c.comp Computable.fst).pair
      ((Computable.const (PolicyShape.siteCode .optionalBoxTail)).pair
        ((Computable.const 2).pair tape.to_comp)))).to₂
  have call := Partrec.bind (numeralPartrec.comp c n.to_comp)
    (partialOnSome (Computable.snd : Computable (Prod.snd : A × Option Nat → Option Nat))
      ((expansion.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂)).to₂
  have z := (Primrec.option_some.comp (nodePrim (Primrec.const 4) f g)).to_comp.partrec
  have normalized : Partrec (fun p : A =>
      (numeral p.1 p.2.1).bind fun
        | none => Part.some none
        | some num => PolicyIndexedShape.macroCode
            (p.1,PolicyShape.siteCode .optionalBoxTail,2,[p.2.2.1,p.2.2.2,num])) :=
    call.of_eq (by
      intro p
      apply congrArg (fun k => (numeral p.1 p.2.1).bind k)
      funext out
      cases out <;> rfl)
  exact partChoose (Primrec.eq.comp n (Primrec.const 0)) z normalized

theorem recursorPartrec : Partrec (fun p : Code × Nat × Nat =>
    (numeral p.1 2).map (Option.map (recursorFrom p.2.1 p.2.2))) := by
  let A := Code × Nat × Nat
  let T := A × Nat
  have old : Computable (fun p : T => p.1.2) := Computable.snd.comp Computable.fst
  have input : Computable (fun p : T => p.1.2.1) := Computable.fst.comp old
  have output : Computable (fun p : T => p.1.2.2) := Computable.snd.comp old
  have args : Computable (fun p : T => (p.1.2.1,p.1.2.2,p.2)) :=
    input.pair (output.pair Computable.snd)
  have fields : Computable₂ (fun (p : A) (v : Nat) => recursorFrom p.2.1 p.2.2 v) :=
    (recFieldsPrim.to_comp.comp args).to₂
  exact partialMapSome (numeralPartrec.comp Computable.fst (Computable.const 2)) fields

theorem applicationPartrec : Partrec (fun p : Code × Nat × Nat × List Nat × List Nat =>
    (tailCode p.1 p.2.2.1 (p.2.2.2.1.getD 0 0) (p.2.2.2.2.getD 0 0)).map
      (Option.map (applicationFrom p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))) := by
  let A := Code × Nat × Nat × List Nat × List Nat
  have raw : Computable (Prod.snd : A → Nat × Nat × List Nat × List Nat) := Computable.snd
  have ar : Computable (fun p : A => p.2.2.1) := Computable.fst.comp (Computable.snd.comp raw)
  have pair : Computable (fun p : A => p.2.2.2) := Computable.snd.comp (Computable.snd.comp raw)
  have first (q : A → List Nat) (hq : Computable q) : Computable (fun p => (q p).getD 0 0) :=
    (Primrec.list_getD 0).to_comp.comp hq (Computable.const 0)
  have tail := tailPartrec.comp ((Computable.fst : Computable (Prod.fst : A → Code)).pair
    (ar.pair ((first _ (Computable.fst.comp pair)).pair (first _ (Computable.snd.comp pair)))))
  have fields : Computable₂ (fun (p : A) (t : Nat) =>
      applicationFrom p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 t) := by
    /- Associate the final scalar inside the retained vector fields. -/
    have data : Computable (fun p : A × Nat => p.1.2) := raw.comp Computable.fst
    have r := Computable.fst.comp data
    have a := Computable.fst.comp (Computable.snd.comp data)
    have f := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp data))
    have g := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp data))
    exact (appFieldsPrim.to_comp.comp (r.pair (a.pair (f.pair (g.pair Computable.snd))))).to₂
  exact partialMapSome tail fields

end LogicLineages.StandardControlCurrent.PolicyIndexedAssignment
