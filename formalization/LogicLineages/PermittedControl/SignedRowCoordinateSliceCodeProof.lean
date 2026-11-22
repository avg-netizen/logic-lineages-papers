module
public import LogicLineages.PermittedControl.SignedRowCoordinateSliceTargets
import LogicLineages.PermittedControl.FiniteStripCollectorRecoveryEffectiveProof
import LogicLineages.PermittedControl.FiniteStripCollectorRecoveryReadProof
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.SignedRowCoordinateSlice
open OrdinalComparison PreparedProjection FiniteStripCollectorRecovery
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof
open MixedSameRankResidue (WeightedOperand WeightedCode encodeWeighted)

private abbrev Hit := Nat × Nat
private abbrev State := WeightedCode × Result LowerOperandCode
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
  let Input := (Update × Option Hit) × Hit
  have fold : Primrec (fun p : Input =>
      (p.1.1.2.1 + p.1.1.1.1 * (p.2.2 : Int),p.1.1.2.2)) := by
    have residual : Primrec (fun p : Input => p.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have weight : Primrec (fun p : Input => p.1.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have value : Primrec (fun p : Input => p.2.2) := Primrec.snd.comp Primrec.snd
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

private def withHits (p : State) (hits : List Hit) : Result LowerOperandCode :=
  p.2.map (fun r => r.map (fun rest => amend (p.1,rest) hits.head?))

private theorem withHitsPrimitive : Primrec₂ withHits := by
  let Input := (State × List Hit) × Residual LowerOperandCode
  have head : Primrec (fun p : Input => p.1.2.head?) :=
    Primrec.list_head?.comp (Primrec.snd.comp Primrec.fst)
  have term : Primrec (fun p : Input => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have update : Primrec (fun p : Input => amend (p.1.1.1,p.2) p.1.2.head?) :=
    amendPrimitive.comp (term.pair Primrec.snd) head
  exact mapReadPrimitive _ _ (Primrec.snd.comp Primrec.fst) update.to₂

private def withPresent (p : State) (status : Option (List Hit)) : Result LowerOperandCode :=
  status.elim (some none) (withHits p)

private theorem withPresentPrimitive : Primrec₂ withPresent := by
  apply (Primrec.option_casesOn Primrec.snd (Primrec.const (some none))
    (withHitsPrimitive.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)).of_eq
  rintro ⟨p,head⟩
  cases head <;> rfl

private theorem stepPrimitive :
    Primrec (fun p : State × ReadResult => step p.1.1 p.2 p.1.2) := by
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

private theorem sliceComputable (f : Nat → Nat) (hf : Computable f) : Computable (sliceCode f) := by
  let Fold := RawArgs × (WeightedCode × Result LowerOperandCode)
  have rank : Computable (fun p : Fold => p.1.1) := Computable.fst.comp Computable.fst
  have input : Computable (fun p : Fold => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have term : Computable (fun p : Fold => p.2.1) := Computable.fst.comp Computable.snd
  have tail : Computable (fun p : Fold => p.2.2) := Computable.snd.comp Computable.snd
  have name : Computable (fun p : Fold => ((1,p.2.1.2) : NamedCode)) :=
    (Computable.const 1).pair (Computable.snd.comp term)
  have read := (collectorEffective f hf).1.comp (rank.pair input) name
  have next : Computable₂ (fun (p : RawArgs) (q : WeightedCode × Result LowerOperandCode) =>
      step q.1 (readCode f p.1 p.2.1 (1,q.1.2)) q.2) :=
    (stepPrimitive.to_comp.comp ((term.pair tail).pair read)).to₂
  have constant : Computable (fun p : RawArgs => p.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have base : Computable (fun p : RawArgs => (some (some (p.2.2.1,[])) : Result LowerOperandCode)) :=
    Computable.option_some.comp (Computable.option_some.comp (constant.pair (Computable.const [])))
  have terms : Computable (fun p : RawArgs => p.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  exact (LayeredComparison.BalancedBoxEvaluation.Graph.computable_foldr
    (default : WeightedCode) terms base next).of_eq (fun _ => rfl)

private theorem stepCode (t : WeightedOperand) (head : ReadResult) (tail : Result LowerOperand) :
    step (encodeWeighted t) head (tail.map (Option.map encodeResidual)) =
      (step t head tail).map (Option.map encodeResidual) := by
  cases head with
  | none => rfl
  | some status =>
    cases status with
    | none => rfl
    | some hits =>
      cases tail with
      | none => rfl
      | some service =>
        cases service with
        | none => rfl
        | some rest =>
          cases hits with
          | nil => rfl
          | cons hit hs => cases hit <;> rfl

private theorem sliceLiteral (f : Nat → Nat) (rank a : Nat) (c : Int)
    (terms : List WeightedOperand) :
    sliceCode f (rank,a,c,terms.map encodeWeighted) =
      (slice f rank a c terms).map (Option.map encodeResidual) := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    change step (encodeWeighted t) (readCode f rank a (encodeRequest (1,t.2)))
      (sliceCode f (rank,a,c,ts.map encodeWeighted)) =
        (step t (expectedRead f rank a (1,t.2)) (slice f rank a c ts)).map
          (Option.map encodeResidual)
    rw [read_code,ih,stepCode]

theorem codeExact : CodeExact := ⟨sliceComputable,sliceLiteral⟩

end LogicLineages.PermittedControl.SignedRowCoordinateSlice
