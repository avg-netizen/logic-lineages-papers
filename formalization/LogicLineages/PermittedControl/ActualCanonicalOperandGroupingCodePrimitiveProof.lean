module
public import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingCodeTargets
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalOperandGroupingCode
open OrdinalComparison.LayeredComparison
open PreparedProjection ActualCanonicalOperandGrouping

private abbrev K := LowerOperandCode
private abbrev Keys := List K

private theorem anyKeyPrimitive :
    Primrec (fun p : K × Keys => p.2.any (fun key => decide (key = p.1))) := by
  let A := K × Keys
  let P := A × (K × Bool)
  have needle : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
  have item : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have acc : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have next : Primrec (fun p : P => decide (p.2.1 = p.1.1) || p.2.2) :=
    Primrec.or.comp ((Primrec.eq.comp item needle).decide) acc
  have fold := Primrec.list_foldr (Primrec.snd : Primrec (Prod.snd : A → Keys))
    (Primrec.const false) next.to₂
  apply fold.of_eq
  intro p
  generalize p.2 = keys
  induction keys with
  | nil => rfl
  | cons key keys ih => simp only [List.foldr_cons,List.any_cons,ih]

private theorem dedupKeyPrimitive : Primrec (List.dedup : Keys → Keys) := by
  let P := Keys × (K × Keys)
  have key : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have tailKeys : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  let advance (key : K) (acc : Keys) : Keys :=
    if acc.any (fun k => decide (k = key)) then acc else key :: acc
  have step : Primrec (fun p : P => advance p.2.1 p.2.2) := by
    apply (Primrec.cond (anyKeyPrimitive.comp (key.pair tailKeys)) tailKeys
      (Primrec.list_cons.comp key tailKeys)).of_eq
    intro p
    change (bif p.2.2.any (fun k => decide (k = p.2.1)) then p.2.2 else p.2.1 :: p.2.2) =
      (if p.2.2.any (fun k => decide (k = p.2.1)) = true then p.2.2 else p.2.1 :: p.2.2)
    generalize p.2.2.any (fun k => decide (k = p.2.1)) = seen
    cases seen <;> rfl
  have fold : Primrec (fun keys : Keys => keys.foldr advance []) :=
    Primrec.list_foldr (Primrec.id : Primrec (id : Keys → Keys))
      (Primrec.const ([] : Keys)) step.to₂
  apply fold.of_eq
  intro keys
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      change advance key (keys.foldr advance []) = (key::keys).dedup
      rw [ih,List.dedup_cons']
      dsimp only [advance]
      have mem : keys.dedup.any (fun k => decide (k = key)) = true ↔ key ∈ keys.dedup := by
        simp only [List.any_eq_true,decide_eq_true_eq]
        constructor
        · rintro ⟨k,used,rfl⟩
          exact used
        · intro used
          exact ⟨key,used,rfl⟩
      by_cases used : key ∈ keys.dedup
      · simp only [mem.mpr used,if_pos used,if_true]
      · have absent : keys.dedup.any (fun k => decide (k = key)) = false :=
          Bool.eq_false_iff.mpr (fun found => used (mem.mp found))
        simp only [absent,if_neg used,Bool.false_eq_true,if_false]

private theorem firstKeyPrimitive : Primrec (firstKeys : Keys → Keys) :=
  Primrec.list_reverse.comp (dedupKeyPrimitive.comp Primrec.list_reverse)

private theorem weightPrimitive :
    Primrec (fun p : List RawTerm × K => signedWeight p.1 p.2) := by
  let A := List RawTerm × K
  let P := A × (RawTerm × Int)
  have needle : Primrec (fun p : P => p.1.2) := Primrec.snd.comp Primrec.fst
  have item : Primrec (fun p : P => p.2.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have coeff : Primrec (fun p : P => p.2.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have acc : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have summand : Primrec (fun p : P => if p.2.1.2 = p.1.2 then p.2.1.1 else (0 : Int)) :=
    Primrec.ite (Primrec.eq.comp item needle) coeff (Primrec.const 0)
  have step := IntegerAlgorithms.Proof.add_primitive.comp summand acc
  have fold := Primrec.list_foldr (Primrec.fst : Primrec (Prod.fst : A → List RawTerm))
    (Primrec.const (0 : Int)) step.to₂
  apply fold.of_eq
  intro p
  rcases p with ⟨terms,key⟩
  induction terms with
  | nil => rfl
  | cons t terms ih =>
      simp only [signedWeight,List.foldr_cons,List.map_cons,List.sum_cons] at ih ⊢
      rw [ih]

theorem groupRawPrimitive : Primrec groupRaw := by
  let A := List RawTerm
  let P := A × K
  have keys : Primrec (fun ts : A => ts.map Prod.snd) :=
    Primrec.list_map Primrec.id (Primrec.snd.comp (Primrec.snd : Primrec (Prod.snd : A × RawTerm → RawTerm))).to₂
  have make : Primrec (fun p : P => (signedWeight p.1 p.2,p.2)) :=
    weightPrimitive.pair Primrec.snd
  have grouped : Primrec (fun ts : A =>
      (firstKeys (ts.map Prod.snd)).map (fun k => (signedWeight ts k,k))) :=
    Primrec.list_map (firstKeyPrimitive.comp keys) make.to₂
  have nonzero : PrimrecPred (fun t : RawTerm => t.1 ≠ 0) :=
    (Primrec.eq.comp Primrec.fst (Primrec.const (0 : Int))).not
  exact (Primrec.listFilter nonzero).comp grouped

theorem groupCheckedRawPrimitive : Primrec₂ groupCheckedRaw := by
  let P := Bool × List RawTerm
  have check : Primrec (Prod.fst : P → Bool) := Primrec.fst
  have group : Primrec (fun p : P => groupRaw p.2) := groupRawPrimitive.comp Primrec.snd
  have present : Primrec (fun p : P => some (groupRaw p.2)) := Primrec.option_some_iff.mpr group
  apply (Primrec.cond check present (Primrec.const none)).to₂.of_eq
  intro checked terms
  cases checked <;> rfl

theorem groupCodePrimitive : Primrec groupCode := by
  let A := Bool × Nat
  let P := A × List RawTerm
  have decode : Primrec (fun p : A => (Encodable.decode p.2 : Option (List RawTerm))) :=
    Primrec.decode.comp Primrec.snd
  have guard : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
  have run : Primrec (fun p : P => groupCheckedRaw p.1.1 p.2) :=
    groupCheckedRawPrimitive.comp guard Primrec.snd
  have encode : Primrec (fun ts : List RawTerm => Encodable.encode ts) := Primrec.encode
  have packed : Primrec (fun p : P => (groupCheckedRaw p.1.1 p.2).map Encodable.encode) :=
    (Primrec.option_map₁ encode).comp run
  have machine := Primrec.option_casesOn decode (Primrec.const (none : Option Nat)) packed.to₂
  apply machine.of_eq
  intro p
  unfold groupCode
  cases (Encodable.decode p.2 : Option (List RawTerm)) <;> rfl

theorem exactGroupingCodePrimitive : ExactGroupingCodePrimitive :=
  ⟨groupRawPrimitive,groupCheckedRawPrimitive,groupCodePrimitive⟩

end LogicLineages.PermittedControl.ActualCanonicalOperandGroupingCode
