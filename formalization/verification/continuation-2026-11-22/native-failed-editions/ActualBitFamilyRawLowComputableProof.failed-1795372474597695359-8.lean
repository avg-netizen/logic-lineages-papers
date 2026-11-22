module
public import LogicLineages.PermittedControl.ActualBitFamilyRawLowTargets
import LogicLineages.PermittedControl.SignedRowCoordinateSliceStatementChecks
import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationGraphProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawLow
open OrdinalComparison
open HeterogeneousSignedMatrixSlice (RawRow RawResult TestCode)
open ActualBitFamilyRawLayout (RawBitRow RawFamily)
open PreparedProjection (LowerOperandCode)
open SignedRowCoordinateSlice (Residual Result)
open StatementChecks (fixed_signedRowCoordinateSliceCodeExact)
open LayeredComparison.BalancedBoxEvaluation.Graph (computable_foldr)

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
  let P := A × RawBitRow
  let Q := P × List RawBitRow
  have onTail : Primrec (fun p : P => p.1.2) := Primrec.snd.comp Primrec.fst
  have row : Primrec (fun p : Q => p.1.2) := Primrec.snd.comp Primrec.fst
  have rows : Primrec (fun p : Q => p.2) := Primrec.snd
  have consRows : Primrec (fun p : P => p.1.2.map (List.cons p.2)) :=
    Primrec.option_map onTail (Primrec.list_cons.comp row rows).to₂
  have all : Primrec (fun p : A => joinClause p.1 p.2) :=
    Primrec.option_bind Primrec.fst consRows.to₂
  exact all.to₂

private theorem oneComputable (f : Nat → Nat) (hf : Computable f) : Computable (sliceOne f) := by
  let A := Nat × Nat × RawBitRow
  have name : Computable (fun p : A => p.1) := Computable.fst
  have a : Computable (fun p : A => p.2.1) := Computable.fst.comp Computable.snd
  have row : Computable (fun p : A => p.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have bit : Computable (fun p : A => p.2.2.2) := Computable.snd.comp (Computable.snd.comp Computable.snd)
  have test : Computable (fun p : A => p.2.2.1.1) := Computable.fst.comp row
  have fields : Computable (fun p : A => p.2.2.1.2) := Computable.snd.comp row
  have hit := (fixed_signedRowCoordinateSliceCodeExact.1 f hf).comp (name.pair (a.pair fields))
  exact takeHitPrimitive.to_comp.comp ((test.pair hit).pair bit)

theorem clauseComputable (f : Nat → Nat) (hf : Computable f) : Computable (clauseCode f) := by
  let P := ClauseArgs × (RawBitRow × Option (List RawBitRow))
  have n : Computable (fun p : P => p.1.1) := Computable.fst.comp Computable.fst
  have a : Computable (fun p : P => p.1.2.1) := Computable.fst.comp (Computable.snd.comp Computable.fst)
  have row : Computable (fun p : P => p.2.1) := Computable.fst.comp Computable.snd
  have acc : Computable (fun p : P => p.2.2) := Computable.snd.comp Computable.snd
  have step : Computable (fun p : P => joinClause (sliceOne f (p.1.1,p.1.2.1,p.2.1)) p.2.2) :=
    joinClausePrimitive.to_comp.comp ((oneComputable f hf).comp (n.pair (a.pair row))) acc
  exact computable_foldr (default : RawBitRow) (Computable.snd.comp Computable.snd)
    (Computable.const (some [])) step.to₂

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

theorem familyComputable (f : Nat → Nat) (hf : Computable f) : Computable (familyCode f) := by
  let P := FamilyArgs × List RawBitRow
  have n : Computable (fun p : P => p.1.1) := Computable.fst.comp Computable.fst
  have a : Computable (fun p : P => p.1.2.1) := Computable.fst.comp (Computable.snd.comp Computable.fst)
  have clause : Computable (fun p : P => p.2) := Computable.snd
  have item := (clauseComputable f hf).comp (n.pair (a.pair clause))
  have source : Computable (fun p : FamilyArgs => p.2.2) := Computable.snd.comp Computable.snd
  have collect : Primrec (fun xs : List (Option (List RawBitRow)) => xs.filterMap id) :=
    Primrec.listFilterMap Primrec.id Primrec.snd
  apply (collect.to_comp.comp (computableMap ([] : List RawBitRow) source item.to₂)).of_eq
  intro p
  unfold familyCode
  generalize p.2.2 = clauses
  induction clauses with
  | nil => rfl
  | cons c cs ih =>
      cases h : clauseCode f (p.1,p.2.1,c) <;> simp [h,ih]

theorem stripsComputable (f : Nat → Nat) (hf : Computable f) : Computable (stripsCode f) := by
  let P := FamilyArgs × Nat
  have n : Computable (fun p : P => p.1.1) := Computable.fst.comp Computable.fst
  have a : Computable (fun p : P => p.2) := Computable.snd
  have raw : Computable (fun p : P => p.1.2.2) := Computable.snd.comp (Computable.snd.comp Computable.fst)
  have bound : Computable (fun p : FamilyArgs => p.2.1) := Computable.fst.comp Computable.snd
  have digits := Primrec.list_range.to_comp.comp bound
  exact computableMap 0 digits (a.pair ((familyComputable f hf).comp (n.pair (a.pair raw)))).to₂

theorem exactRawLowCode : ExactRawLowCode :=
  fun f hf => ⟨clauseComputable f hf,familyComputable f hf,stripsComputable f hf⟩

end LogicLineages.PermittedControl.ActualBitFamilyRawLow
