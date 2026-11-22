module
public import LogicLineages.PermittedControl.ActualBitFamilyRawDriverTargets
import LogicLineages.PermittedControl.ActualBitFamilyRawLayoutPrimitiveProof
import LogicLineages.PermittedControl.ActualBitFamilyRawLowComputableProof
import LogicLineages.PermittedControl.ActualBitFamilyRawClosedPrimitiveProof
import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationGraphProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawDriver
open OrdinalComparison.LayeredComparison.BalancedBoxEvaluation.Graph (computable_foldr)
open ActualBitFamilyRawLayout (RawFamily names namesPrimitive)
open ActualBitFamilyRawLow (Branch stripsCode stripsComputable)
open ActualBitFamilyRawClosed (closedCode exactClosedRawEffectivity)

private theorem mappedSecond {A B : Type} [Primcodable A] [Primcodable B] :
    Primrec (fun xs : List (A × B) => xs.map Prod.snd) := by
  have project : Primrec (fun p : List (A × B) × (A × B) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact Primrec.list_map Primrec.id project.to₂

private theorem flatMapComputable {A D E : Type} [Primcodable A] [Primcodable D] [Primcodable E]
    (zero : D) {source : A → List D} {emit : A → D → List E}
    (hs : Computable source) (he : Computable₂ emit) :
    Computable (fun a => (source a).flatMap (emit a)) := by
  let P := A × (D × List E)
  have ctx : Computable (Prod.fst : P → A) := Computable.fst
  have x : Computable (fun p : P => p.2.1) := Computable.fst.comp Computable.snd
  have tail : Computable (fun p : P => p.2.2) := Computable.snd.comp Computable.snd
  have step : Computable (fun p : P => emit p.1 p.2.1 ++ p.2.2) :=
    Computable.list_append.comp (he.comp ctx x) tail
  apply (computable_foldr zero hs (Computable.const []) step.to₂).of_eq
  intro a
  induction source a with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons,List.flatMap_cons,ih]

private theorem anyPrimitive {A : Type} [Primcodable A] {p : A → Bool}
    (hp : Primrec p) : Primrec (fun xs : List A => xs.any p) := by
  have t : Primrec (fun t : A × Bool => p t.1 || t.2) :=
    Primrec.or.comp (hp.comp Primrec.fst) Primrec.snd
  have step : Primrec₂ (fun (_ : List A) (t : A × Bool) => p t.1 || t.2) :=
    (t.comp (Primrec.snd : Primrec (Prod.snd : List A × (A × Bool) → A × Bool))).to₂
  apply (Primrec.list_foldr Primrec.id (Primrec.const false) step).of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (p x || xs.foldr (fun item acc => p item || acc) false) = (p x || xs.any p)
    exact congrArg (fun b => p x || b) ih

private theorem depthPrimitive : Primrec depth :=
  Primrec.list_length.comp namesPrimitive

private theorem zeroPrimitive : Primrec (fun r : RawFamily => decide (depth r = 0)) :=
  (Primrec.eq.comp depthPrimitive (Primrec.const 0)).decide

private theorem hitPrimitive : Primrec hit :=
  Primrec.and.comp zeroPrimitive exactClosedRawEffectivity.2.2.2.2

private theorem lowComputable (f : Nat → Nat) (hf : Computable f) :
    Computable₂ (lowCode f) := by
  let A := Nat × RawFamily
  let P := A × Nat
  have source : Computable (fun p : A => names p.2) :=
    namesPrimitive.to_comp.comp Computable.snd
  have k : Computable (Prod.snd : P → Nat) := Computable.snd
  have C : Computable (fun p : P => p.1.1) := Computable.fst.comp Computable.fst
  have r : Computable (fun p : P => p.1.2) := Computable.snd.comp Computable.fst
  have list : Computable (fun p : P => stripsCode f (p.2,p.1.1,p.1.2)) :=
    (stripsComputable f hf).comp (k.pair (C.pair r))
  have emit : Computable (fun p : P => (stripsCode f (p.2,p.1.1,p.1.2)).map Prod.snd) :=
    mappedSecond.to_comp.comp list
  exact (flatMapComputable 0 source emit.to₂).to₂

private theorem nextComputable (f : Nat → Nat) (bound : BoundProgram) (high : HighProgram)
    (hf : Computable f) (hb : Computable bound) (hh : Computable high) :
    Computable (nextCode f bound high) := by
  have lowPart := (lowComputable f hf).comp hb Computable.id
  have highPart := hh.comp (hb.pair Computable.id)
  apply (Computable.cond zeroPrimitive.to_comp (Computable.const []) <|
    Computable.list_append.comp lowPart highPart).of_eq
  intro raw
  by_cases h : depth raw = 0 <;> simp [nextCode,h]

private theorem advanceComputable (f : Nat → Nat) (bound : BoundProgram) (high : HighProgram)
    (hf : Computable f) (hb : Computable bound) (hh : Computable high) :
    Computable (advance f bound high) := by
  have tape : Computable (Prod.snd : State → List RawFamily) := Computable.snd
  have hp : Computable (fun s : State => s.2.any hit) := (anyPrimitive hitPrimitive).to_comp.comp tape
  have ok : Computable (fun s : State => s.1 || s.2.any hit) :=
    Primrec.or.to_comp.comp Computable.fst hp
  have next : Computable (fun s : State => s.2.flatMap (nextCode f bound high)) :=
    flatMapComputable ([] : RawFamily) tape
      ((nextComputable f bound high hf hb hh).comp (Computable.snd :
        Computable (Prod.snd : State × RawFamily → RawFamily))).to₂
  exact ok.pair next

private theorem computableIteration {A S V : Type} [Primcodable A] [Primcodable S] [Primcodable V]
    {count : A → Nat} {initial : A → S} {next : S → S} {finish : S → V}
    (hc : Computable count) (hi : Computable initial) (hn : Computable next)
    (hf : Computable finish) :
    Computable (fun a : A => finish (Nat.rec (initial a) (fun _ s => next s) (count a))) := by
  have applyNext : Computable₂ (fun (_ : A) (t : Nat × S) => next t.2) :=
    (hn.comp (Computable.snd.comp Computable.snd) :
      Computable (fun p : A × (Nat × S) => next p.2.2)).to₂
  exact hf.comp (Computable.nat_rec hc hi applyNext)

private theorem solveComputable (f : Nat → Nat) (bound : BoundProgram) (high : HighProgram)
    (hf : Computable f) (hb : Computable bound) (hh : Computable high) :
    Computable (solve f bound high) := by
  have n : Computable (fun raw : RawFamily => depth raw + 1) :=
    (Primrec.succ.comp depthPrimitive).to_comp
  have initial : Computable (fun raw : RawFamily => ((false,[raw]) : State)) :=
    (Computable.const false).pair (Computable.list_cons.comp Computable.id (Computable.const []))
  have advanceWith : Computable (advance f bound high) :=
    advanceComputable f bound high hf hb hh
  have finish : Computable (Prod.fst : State → Bool) := Computable.fst
  exact (computableIteration n initial advanceWith finish).of_eq (fun _ => rfl)

theorem exactDriverEffectivity : ExactDriverEffectivity := solveComputable

end LogicLineages.PermittedControl.ActualBitFamilyRawDriver
