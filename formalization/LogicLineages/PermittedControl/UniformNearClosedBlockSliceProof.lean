module
public import LogicLineages.PermittedControl.SignedRowCoordinateSliceTargets
import LogicLineages.PermittedControl.UniformNearClosedBlockFieldProof
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationGraphProof
import Mathlib.Computability.Primrec.List

/-! Parametric copies of the per-control effectivity of the field read, the
named read (`FiniteStripCollectorRecovery`) and the coordinate slice. -/

public section
namespace LogicLineages.PermittedControl.UniformNearClosedBlock
open OrdinalComparison PreparedProjection FieldComparison
open FiniteStripCollectorRecovery (NamedCode ReadResult operandShape fieldRead readCode)
open SignedRowCoordinateSlice (Residual Result RawArgs step sliceCode)
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof
open MixedSameRankResidue (WeightedCode)

attribute [local irreducible] rawSplitCode rawNormCode rawNormalCode encodedMaximumPredecessor
  encodedFiniteTest encodedFiniteValue Nat.unpair Nat.sqrt fixedEntryClosedScan

variable {α : Type} [Primcodable α]

private theorem shapePrimitive : Primrec operandShape := by
  have ht : Primrec (fun c : LowerOperandCode => c.1) := Primrec.fst
  have hf : Primrec (fun c : LowerOperandCode => c.2.2) := Primrec.snd.comp Primrec.snd
  have hk := Primrec.fst.comp hf
  have ha := Primrec.fst.comp (Primrec.snd.comp hf)
  have hl := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hf))
  have hm := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hf))
  have hz := (Primrec.eq.comp hf (Primrec.const (0,0,0,0))).decide
  have ho := (((Primrec.eq.comp hk (Primrec.const 0)).and
    ((Primrec.eq.comp hl (Primrec.const 0)).and (Primrec.eq.comp hm (Primrec.const 0)))).or
    (Primrec.eq.comp hk (Primrec.const 1))).decide
  have hc := ((Primrec.eq.comp ht (Primrec.const 2)).and
    ((Primrec.eq.comp hk (Primrec.const 1)).and (Primrec.eq.comp ha (Primrec.const 0)))).decide
  exact Primrec.ite (Primrec.eq.comp ht (Primrec.const 0)) hz
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 1)) ho hc)

private theorem computedIf {A B : Type} [Primcodable A] [Primcodable B]
    (p : A → Prop) [DecidablePred p] (hp : PrimrecPred p)
    (u v : A → B) (hu : Computable u) (hv : Computable v) :
    Computable (fun a => if p a then u a else v a) := by
  exact (Computable.cond hp.decide.to_comp hu hv).of_eq (fun a => by simp)

theorem fieldReadParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable (fun x : α × (Nat × LowerOperandCode) => fieldRead (F x.1) x.2.1 x.2.2) := by
  have hc : Computable (fun x : α × (Nat × LowerOperandCode) => x.1) := Computable.fst
  have ha : Computable (fun x : α × (Nat × LowerOperandCode) => x.2.1) := Computable.fst.comp Computable.snd
  have ht : Primrec (fun x : α × (Nat × LowerOperandCode) => x.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hfield : Computable (fun x : α × (Nat × LowerOperandCode) => x.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hl : Computable (fun x : α × (Nat × LowerOperandCode) => x.2.2.2.2.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hfield))
  have hm : Computable (fun x : α × (Nat × LowerOperandCode) => x.2.2.2.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hfield))
  have hcoord : Computable (fun x : α × (Nat × LowerOperandCode) => (some (some x.2.1) : ClosedNaturalFieldResult)) :=
    Computable.option_some.comp (Computable.option_some.comp ha)
  have hvalue : Computable (fun x : α × (Nat × LowerOperandCode) =>
      closedOrdinaryValueField (F x.1) x.2.2.2.2 x.2.1) := by
    have h := (valueFieldParam F hF).comp (hc.pair (hfield.pair ha))
    exact h
  have hcount : Computable (fun x : α × (Nat × LowerOperandCode) =>
      closedOrdinaryCountField (F x.1) (x.2.2.2.2.2.2.1,x.2.2.2.2.2.2.2,x.2.1)) := by
    have h := (countFieldParam F hF).comp (hc.pair (hl.pair (hm.pair ha)))
    exact h
  have h := computedIf (fun x : α × (Nat × LowerOperandCode) => x.2.2.1 = 0)
    (Primrec.eq.comp ht (Primrec.const 0)) _ _ hcoord
    (computedIf (fun x : α × (Nat × LowerOperandCode) => x.2.2.1 = 1)
      (Primrec.eq.comp ht (Primrec.const 1)) _ _ hvalue hcount)
  exact h

private def tagOneP (name : Nat) (v : Option Nat) : Option (List (Nat × Nat)) :=
  v.map (fun b => [(name,b)])
private def tagReadP (name : Nat) (v : ClosedNaturalFieldResult) : ReadResult :=
  v.map (tagOneP name)

private theorem tagOneP_primitive : Primrec₂ tagOneP := by
  have hs : Primrec (fun p : (Nat × Option Nat) × Nat => [(p.1.1,p.2)]) :=
    Primrec.list_cons.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd) (Primrec.const [])
  exact Primrec.option_map Primrec.snd hs.to₂

private theorem tagReadP_primitive : Primrec₂ tagReadP :=
  Primrec.option_map Primrec.snd
    (tagOneP_primitive.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)

theorem readParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable (fun x : α × ((Nat × Nat) × NamedCode) => readCode (F x.1) x.2.1.1 x.2.1.2 x.2.2) := by
  have hn : Primrec (fun x : α × ((Nat × Nat) × NamedCode) => x.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hcode : Primrec (fun x : α × ((Nat × Nat) × NamedCode) => x.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hr : Primrec (fun x : α × ((Nat × Nat) × NamedCode) => x.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp hcode)
  have hx : Primrec (fun x : α × ((Nat × Nat) × NamedCode) => x.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have ha : Primrec (fun x : α × ((Nat × Nat) × NamedCode) => x.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hbad : PrimrecPred (fun x : α × ((Nat × Nat) × NamedCode) => x.2.2.1 = 0 ∨ operandShape x.2.2.2 = false) :=
    (Primrec.eq.comp hn (Primrec.const 0)).or
      (Primrec.eq.comp (shapePrimitive.comp hcode) (Primrec.const false))
  have hskip : PrimrecPred (fun x : α × ((Nat × Nat) × NamedCode) => x.2.2.2.2.1 ≠ x.2.1.1) :=
    (Primrec.eq.comp hr hx).not
  have hfield : Computable (fun x : α × ((Nat × Nat) × NamedCode) => fieldRead (F x.1) x.2.1.2 x.2.2.2) := by
    have h := (fieldReadParam F hF).comp (Computable.fst.pair (ha.to_comp.pair hcode.to_comp))
    exact h
  have hmatched : Computable (fun x : α × ((Nat × Nat) × NamedCode) =>
      tagReadP x.2.2.1 (fieldRead (F x.1) x.2.1.2 x.2.2.2)) :=
    tagReadP_primitive.to_comp.comp hn.to_comp hfield
  have h := computedIf _ hbad _ _ (Computable.const none)
    (computedIf _ hskip _ _ (Computable.const (some (some []))) hmatched)
  exact h

private abbrev Hit := Nat × Nat
private abbrev SState := WeightedCode × Result LowerOperandCode
private abbrev Update := WeightedCode × Residual LowerOperandCode

private def amend (p : Update) (head : Option Hit) : Residual LowerOperandCode :=
  match head with
  | none => (p.2.1,p.1 :: p.2.2)
  | some h => (p.2.1 + p.1.1 * (h.2 : Int),p.2.2)

private theorem amendPrimitive : Primrec₂ amend := by
  have carry : Primrec (fun p : Update × Option Hit => (p.1.2.1,p.1.1 :: p.1.2.2)) := by
    have residual : Primrec (fun p : Update × Option Hit => p.1.2) := Primrec.snd.comp Primrec.fst
    have weight : Primrec (fun p : Update × Option Hit => p.1.1) := Primrec.fst.comp Primrec.fst
    exact (Primrec.fst.comp residual).pair
      (Primrec.list_cons.comp weight (Primrec.snd.comp residual))
  have fold : Primrec (fun p : (Update × Option Hit) × Hit =>
      (p.1.1.2.1 + p.1.1.1.1 * (p.2.2 : Int),p.1.1.2.2)) := by
    have residual : Primrec (fun p : (Update × Option Hit) × Hit => p.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have weight : Primrec (fun p : (Update × Option Hit) × Hit => p.1.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have value : Primrec (fun p : (Update × Option Hit) × Hit => p.2.2) := Primrec.snd.comp Primrec.snd
    exact (add_primitive.comp (Primrec.fst.comp residual)
      (mul_primitive.comp weight (ofNat_primitive.comp value))).pair (Primrec.snd.comp residual)
  apply (Primrec.option_casesOn Primrec.snd carry fold.to₂).of_eq
  rintro ⟨p,head⟩
  cases head <;> rfl

private theorem mapReadPrimitive {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]
    (read : A → Option (Option B)) (update : A → B → C)
    (hr : Primrec read) (hu : Primrec₂ update) :
    Primrec (fun a => (read a).map (fun r => r.map (update a))) := by
  have inner : Primrec (fun p : (A × Option B) × B => update p.1.1 p.2) :=
    hu.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact Primrec.option_map hr (Primrec.option_map Primrec.snd inner.to₂).to₂

private def withHits (p : SState) (hits : List Hit) : Result LowerOperandCode :=
  p.2.map (fun r => r.map (fun rest => amend (p.1,rest) hits.head?))

private theorem withHitsPrimitive : Primrec₂ withHits := by
  have head : Primrec (fun p : (SState × List Hit) × Residual LowerOperandCode => p.1.2.head?) :=
    Primrec.list_head?.comp (Primrec.snd.comp Primrec.fst)
  have term : Primrec (fun p : (SState × List Hit) × Residual LowerOperandCode => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have update : Primrec (fun p : (SState × List Hit) × Residual LowerOperandCode =>
      amend (p.1.1.1,p.2) p.1.2.head?) :=
    amendPrimitive.comp (term.pair Primrec.snd) head
  exact mapReadPrimitive _ _ (Primrec.snd.comp Primrec.fst) update.to₂

private def withPresent (p : SState) (status : Option (List Hit)) : Result LowerOperandCode :=
  status.elim (some none) (withHits p)

private theorem withPresentPrimitive : Primrec₂ withPresent := by
  apply (Primrec.option_casesOn Primrec.snd (Primrec.const (some none))
    (withHitsPrimitive.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)).of_eq
  rintro ⟨p,head⟩
  cases head <;> rfl

private theorem stepPrimitive :
    Primrec (fun p : SState × ReadResult => step p.1.1 p.2 p.1.2) := by
  apply (Primrec.option_casesOn Primrec.snd (Primrec.const none)
    (withPresentPrimitive.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)).of_eq
  rintro ⟨p,head⟩
  cases head with
  | none => rfl
  | some h =>
    cases h with
    | none => rfl
    | some hits =>
      cases hits with
      | nil => rfl
      | cons hit hs => cases hit <;> rfl

theorem sliceParam (F : α → Nat → Nat) (hF : Computable₂ F) :
    Computable (fun x : α × RawArgs => sliceCode (F x.1) x.2) := by
  have rank : Computable (fun p : (α × RawArgs) × (WeightedCode × Result LowerOperandCode) => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have input : Computable (fun p : (α × RawArgs) × (WeightedCode × Result LowerOperandCode) => p.1.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have term : Computable (fun p : (α × RawArgs) × (WeightedCode × Result LowerOperandCode) => p.2.1) :=
    Computable.fst.comp Computable.snd
  have tail : Computable (fun p : (α × RawArgs) × (WeightedCode × Result LowerOperandCode) => p.2.2) :=
    Computable.snd.comp Computable.snd
  have ctx : Computable (fun p : (α × RawArgs) × (WeightedCode × Result LowerOperandCode) => p.1.1) :=
    Computable.fst.comp Computable.fst
  have name : Computable (fun p : (α × RawArgs) × (WeightedCode × Result LowerOperandCode) =>
      ((1,p.2.1.2) : NamedCode)) :=
    (Computable.const 1).pair (Computable.snd.comp term)
  have read : Computable (fun p : (α × RawArgs) × (WeightedCode × Result LowerOperandCode) =>
      readCode (F p.1.1) p.1.2.1 p.1.2.2.1 (1,p.2.1.2)) := by
    have h := (readParam F hF).comp (ctx.pair ((rank.pair input).pair name))
    exact h
  have next : Computable₂ (fun (x : α × RawArgs) (q : WeightedCode × Result LowerOperandCode) =>
      step q.1 (readCode (F x.1) x.2.1 x.2.2.1 (1,q.1.2)) q.2) := by
    have h := stepPrimitive.to_comp.comp ((term.pair tail).pair read)
    exact h.to₂
  have constant : Computable (fun x : α × RawArgs => x.2.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have base : Computable (fun x : α × RawArgs => (some (some (x.2.2.2.1,[])) : Result LowerOperandCode)) :=
    Computable.option_some.comp (Computable.option_some.comp (constant.pair (Computable.const [])))
  have terms : Computable (fun x : α × RawArgs => x.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  exact (LayeredComparison.BalancedBoxEvaluation.Graph.computable_foldr
    (default : WeightedCode) terms base next).of_eq (fun _ => rfl)

end LogicLineages.PermittedControl.UniformNearClosedBlock
