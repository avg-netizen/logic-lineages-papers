module
public import LogicLineages.PermittedControl.UniformNearClosedBlockTargets
import LogicLineages.PermittedControl.UniformNearClosedBlockSliceProof
import LogicLineages.PermittedControl.ActualBitFamilyRawLayoutPrimitiveProof
import LogicLineages.PermittedControl.ActualBitFamilyRawClosedPrimitiveProof
import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationGraphProof
import Mathlib.Computability.Primrec.List

/-! Parametric copies of the per-control effectivity of the raw low code
(#1307) and of the raw driver (#1340). -/

public section
namespace LogicLineages.PermittedControl.UniformNearClosedBlock
open OrdinalComparison
open OrdinalComparison.LayeredComparison.BalancedBoxEvaluation.Graph (computable_foldr)
open HeterogeneousSignedMatrixSlice (RawRow RawResult TestCode)
open PreparedProjection (LowerOperandCode)
open SignedRowCoordinateSlice (Residual Result sliceCode)
open ActualBitFamilyRawLayout (RawBitRow RawFamily names namesPrimitive)
open ActualBitFamilyRawLow (takeHit joinClause sliceOne clauseCode familyCode stripsCode
  ClauseArgs FamilyArgs Branch)
open ActualBitFamilyRawDriver (BoundProgram HighProgram State depth hit lowCode nextCode advance scan solve)
open ActualBitFamilyRawClosed (closedCode exactClosedRawEffectivity)

attribute [local irreducible] rawSplitCode rawNormCode rawNormalCode encodedMaximumPredecessor
  encodedFiniteTest encodedFiniteValue Nat.unpair Nat.sqrt fixedEntryClosedScan sliceCode

variable {α : Type} [Primcodable α]

private theorem takeHitPrimitive : Primrec takeHit := by
  let A := RawResult × Bool
  let P := A × Option (Residual LowerOperandCode)
  let Q := P × Residual LowerOperandCode
  have status : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have innerStatus : Primrec (fun p : P => p.2) := Primrec.snd
  have test : Primrec (fun p : Q => p.1.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have bit : Primrec (fun p : Q => p.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have out : Primrec (fun p : Q => p.2) := Primrec.snd
  have inner : Primrec (fun p : P =>
      p.2.map (fun out => ((p.1.1.1,out),p.1.2))) :=
    Primrec.option_map innerStatus ((test.pair out).pair bit).to₂
  exact Primrec.option_bind status inner.to₂

private theorem joinClausePrimitive : Primrec₂ joinClause := by
  let A := Option RawBitRow × Option (List RawBitRow)
  let P := RawBitRow × Option (List RawBitRow)
  let Q := P × List RawBitRow
  have row : Primrec (fun p : Q => p.1.1) := Primrec.fst.comp Primrec.fst
  have rows : Primrec (Prod.snd : Q → List RawBitRow) := Primrec.snd
  have consTail : Primrec (fun p : P => p.2.map (List.cons p.1)) :=
    Primrec.option_map Primrec.snd (Primrec.list_cons.comp row rows).to₂
  have consRows : Primrec₂ (fun (p : A) (row : RawBitRow) =>
      p.2.map (List.cons row)) :=
    (consTail.comp (Primrec.snd.pair (Primrec.snd.comp Primrec.fst)) :
      Primrec (fun p : A × RawBitRow => p.1.2.map (List.cons p.2))).to₂
  have all : Primrec (fun p : A => joinClause p.1 p.2) :=
    Primrec.option_bind Primrec.fst consRows
  exact all.to₂

private theorem computableMap {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]
    (zero : B) {source : A → List B} {child : A → B → C}
    (hs : Computable source) (hc : Computable₂ child) :
    Computable (fun a => (source a).map (child a)) := by
  let P := A × (B × List C)
  have root : Computable (fun p : P => p.1) := Computable.fst
  have item : Computable (fun p : P => p.2.1) := Computable.fst.comp Computable.snd
  have acc : Computable (fun p : P => p.2.2) := Computable.snd.comp Computable.snd
  have step : Computable (fun p : P => child p.1 p.2.1 :: p.2.2) :=
    Primrec.list_cons.to_comp.comp (hc.comp root item) acc
  apply (computable_foldr zero hs (Computable.const []) step.to₂).of_eq
  intro a
  induction source a with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.foldr_cons, ih]

theorem sliceOneParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable (fun x : α × (Nat × Nat × RawBitRow) => sliceOne (F x.1) x.2) := by
  have ctx : Computable (fun x : α × (Nat × Nat × RawBitRow) => x.1) := Computable.fst
  have name : Computable (fun x : α × (Nat × Nat × RawBitRow) => x.2.1) := Computable.fst.comp Computable.snd
  have a : Computable (fun x : α × (Nat × Nat × RawBitRow) => x.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have row : Computable (fun x : α × (Nat × Nat × RawBitRow) => x.2.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have bit : Computable (fun x : α × (Nat × Nat × RawBitRow) => x.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have test : Computable (fun x : α × (Nat × Nat × RawBitRow) => x.2.2.2.1.1) := Computable.fst.comp row
  have fields : Computable (fun x : α × (Nat × Nat × RawBitRow) => x.2.2.2.1.2) := Computable.snd.comp row
  have hitc : Computable (fun x : α × (Nat × Nat × RawBitRow) =>
      sliceCode (F x.1) (x.2.1,x.2.2.1,x.2.2.2.1.2)) := by
    have h := (sliceParam F hF).comp (ctx.pair (name.pair (a.pair fields)))
    exact h
  have h := takeHitPrimitive.to_comp.comp ((test.pair hitc).pair bit)
  exact h

theorem clauseParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable (fun x : α × ClauseArgs => clauseCode (F x.1) x.2) := by
  have ctx : Computable (fun p : (α × ClauseArgs) × (RawBitRow × Option (List RawBitRow)) => p.1.1) :=
    Computable.fst.comp Computable.fst
  have n : Computable (fun p : (α × ClauseArgs) × (RawBitRow × Option (List RawBitRow)) => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have a : Computable (fun p : (α × ClauseArgs) × (RawBitRow × Option (List RawBitRow)) => p.1.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have row : Computable (fun p : (α × ClauseArgs) × (RawBitRow × Option (List RawBitRow)) => p.2.1) :=
    Computable.fst.comp Computable.snd
  have acc : Computable (fun p : (α × ClauseArgs) × (RawBitRow × Option (List RawBitRow)) => p.2.2) :=
    Computable.snd.comp Computable.snd
  have one : Computable (fun p : (α × ClauseArgs) × (RawBitRow × Option (List RawBitRow)) =>
      sliceOne (F p.1.1) (p.1.2.1,p.1.2.2.1,p.2.1)) := by
    have h := (sliceOneParam F hF).comp (ctx.pair (n.pair (a.pair row)))
    exact h
  have step : Computable (fun p : (α × ClauseArgs) × (RawBitRow × Option (List RawBitRow)) =>
      joinClause (sliceOne (F p.1.1) (p.1.2.1,p.1.2.2.1,p.2.1)) p.2.2) :=
    joinClausePrimitive.to_comp.comp one acc
  have rows : Computable (fun x : α × ClauseArgs => x.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  exact computable_foldr (default : RawBitRow) rows (Computable.const (some [])) step.to₂

theorem familyParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable (fun x : α × FamilyArgs => familyCode (F x.1) x.2) := by
  have ctx : Computable (fun p : (α × FamilyArgs) × List RawBitRow => p.1.1) :=
    Computable.fst.comp Computable.fst
  have n : Computable (fun p : (α × FamilyArgs) × List RawBitRow => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have a : Computable (fun p : (α × FamilyArgs) × List RawBitRow => p.1.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have clause : Computable (fun p : (α × FamilyArgs) × List RawBitRow => p.2) := Computable.snd
  have item : Computable (fun p : (α × FamilyArgs) × List RawBitRow =>
      clauseCode (F p.1.1) (p.1.2.1,p.1.2.2.1,p.2)) := by
    have h := (clauseParam F hF).comp (ctx.pair (n.pair (a.pair clause)))
    exact h
  have source : Computable (fun x : α × FamilyArgs => x.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have collect : Primrec (fun xs : List (Option (List RawBitRow)) => xs.filterMap id) :=
    Primrec.listFilterMap Primrec.id Primrec.snd
  apply (collect.to_comp.comp (computableMap ([] : List RawBitRow) source item.to₂)).of_eq
  intro x
  unfold familyCode
  generalize x.2.2.2 = clauses
  induction clauses with
  | nil => rfl
  | cons c cs ih =>
      cases h : clauseCode (F x.1) (x.2.1,x.2.2.1,c) <;> simp [h,ih]

theorem stripsParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable (fun x : α × FamilyArgs => stripsCode (F x.1) x.2) := by
  have ctx : Computable (fun p : (α × FamilyArgs) × Nat => p.1.1) := Computable.fst.comp Computable.fst
  have n : Computable (fun p : (α × FamilyArgs) × Nat => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have a : Computable (fun p : (α × FamilyArgs) × Nat => p.2) := Computable.snd
  have raw : Computable (fun p : (α × FamilyArgs) × Nat => p.1.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have fam : Computable (fun p : (α × FamilyArgs) × Nat => familyCode (F p.1.1) (p.1.2.1,p.2,p.1.2.2.2)) := by
    have h := (familyParam F hF).comp (ctx.pair (n.pair (a.pair raw)))
    exact h
  have bound : Computable (fun x : α × FamilyArgs => x.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have digits := Primrec.list_range.to_comp.comp bound
  exact computableMap 0 digits (a.pair fam).to₂

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

theorem lowParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable (fun x : α × (Nat × RawFamily) => lowCode (F x.1) x.2.1 x.2.2) := by
  have source : Computable (fun x : α × (Nat × RawFamily) => names x.2.2) :=
    namesPrimitive.to_comp.comp (Computable.snd.comp Computable.snd)
  have ctx : Computable (fun p : (α × (Nat × RawFamily)) × Nat => p.1.1) := Computable.fst.comp Computable.fst
  have k : Computable (fun p : (α × (Nat × RawFamily)) × Nat => p.2) := Computable.snd
  have C : Computable (fun p : (α × (Nat × RawFamily)) × Nat => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have r : Computable (fun p : (α × (Nat × RawFamily)) × Nat => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have list : Computable (fun p : (α × (Nat × RawFamily)) × Nat => stripsCode (F p.1.1) (p.2,p.1.2.1,p.1.2.2)) := by
    have h := (stripsParam F hF).comp (ctx.pair (k.pair (C.pair r)))
    exact h
  have emit : Computable (fun p : (α × (Nat × RawFamily)) × Nat =>
      (stripsCode (F p.1.1) (p.2,p.1.2.1,p.1.2.2)).map Prod.snd) :=
    mappedSecond.to_comp.comp list
  exact flatMapComputable 0 source emit.to₂

theorem nextParam (F : α → Nat → Nat) (bound : α → RawFamily → Nat) (high : HighProgram)
    (hF : Computable₂ F) (hb : Computable₂ bound) (hh : Computable high) :
    Computable (fun x : α × RawFamily => nextCode (F x.1) (bound x.1) high x.2) := by
  have Cc : Computable (fun x : α × RawFamily => bound x.1 x.2) := hb.comp Computable.fst Computable.snd
  have lowPart : Computable (fun x : α × RawFamily => lowCode (F x.1) (bound x.1 x.2) x.2) := by
    have h := (lowParam F hF).comp (Computable.fst.pair (Cc.pair Computable.snd))
    exact h
  have highPart : Computable (fun x : α × RawFamily => high (bound x.1 x.2,x.2)) :=
    hh.comp (Cc.pair Computable.snd)
  have zero : Computable (fun x : α × RawFamily => decide (depth x.2 = 0)) :=
    zeroPrimitive.to_comp.comp Computable.snd
  apply (Computable.cond zero (Computable.const []) <|
    Computable.list_append.comp lowPart highPart).of_eq
  intro x
  by_cases h : depth x.2 = 0 <;> simp [nextCode,h]

theorem advanceParam (F : α → Nat → Nat) (bound : α → RawFamily → Nat) (high : HighProgram)
    (hF : Computable₂ F) (hb : Computable₂ bound) (hh : Computable high) :
    Computable (fun x : α × State => advance (F x.1) (bound x.1) high x.2) := by
  have tape : Computable (fun x : α × State => x.2.2) := Computable.snd.comp Computable.snd
  have hp : Computable (fun x : α × State => x.2.2.any hit) := (anyPrimitive hitPrimitive).to_comp.comp tape
  have ok : Computable (fun x : α × State => x.2.1 || x.2.2.any hit) :=
    Primrec.or.to_comp.comp (Computable.fst.comp Computable.snd) hp
  have nx : Computable₂ (fun (x : α × State) (raw : RawFamily) => nextCode (F x.1) (bound x.1) high raw) := by
    have h := (nextParam F bound high hF hb hh).comp
      ((Computable.fst.comp (Computable.fst : Computable (Prod.fst : (α × State) × RawFamily → α × State))).pair
        (Computable.snd : Computable (Prod.snd : (α × State) × RawFamily → RawFamily)))
    exact h.to₂
  have next : Computable (fun x : α × State => x.2.2.flatMap (nextCode (F x.1) (bound x.1) high)) :=
    flatMapComputable ([] : RawFamily) tape nx
  have h := ok.pair next
  exact h

theorem solveParam (F : α → Nat → Nat) (bound : α → RawFamily → Nat) (high : HighProgram)
    (hF : Computable₂ F) (hb : Computable₂ bound) (hh : Computable high) :
    Computable (fun x : α × RawFamily => solve (F x.1) (bound x.1) high x.2) := by
  have n : Computable (fun x : α × RawFamily => depth x.2 + 1) :=
    (Primrec.succ.comp depthPrimitive).to_comp.comp Computable.snd
  have initial : Computable (fun x : α × RawFamily => ((false,[x.2]) : State)) :=
    (Computable.const false).pair (Computable.list_cons.comp Computable.snd (Computable.const []))
  have stepc : Computable₂ (fun (x : α × RawFamily) (t : Nat × State) => advance (F x.1) (bound x.1) high t.2) := by
    have h := (advanceParam F bound high hF hb hh).comp
      ((Computable.fst.comp (Computable.fst : Computable (Prod.fst : (α × RawFamily) × (Nat × State) → α × RawFamily))).pair
        (Computable.snd.comp (Computable.snd : Computable (Prod.snd : (α × RawFamily) × (Nat × State) → Nat × State))))
    exact h.to₂
  have iter := Computable.nat_rec n initial stepc
  exact (Computable.fst.comp iter).of_eq (fun _ => rfl)

theorem parametricSolveEffectivity : ParametricSolveEffectivity := by
  intro α _ F bound high hF hb hh
  exact solveParam F bound high hF hb hh

end LogicLineages.PermittedControl.UniformNearClosedBlock
