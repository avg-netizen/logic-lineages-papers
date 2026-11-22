module
public import LogicLineages.PermittedControl.MixedRankResidueTargets
import LogicLineages.PermittedControl.MixedSameRankResidueStatementChecks
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.MixedRankResidue
open OrdinalComparison PreparedProjection
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof
open MixedSameRankResidue (WeightedOperand WeightedCode encodeWeighted weightedResidue weightedResidueCode)
open StatementChecks (fixed_mixedSameRankResidueCodeExact)

private theorem rankPresentPrimitive : Primrec₂ rankPresent := by
  let Args := Nat × List Nat
  let Step := Args × (Nat × Bool)
  have rank : Primrec (fun p : Step => p.1.1) := Primrec.fst.comp Primrec.fst
  have next : Primrec (fun p : Step => p.2.1) := Primrec.fst.comp Primrec.snd
  have acc : Primrec (fun p : Step => p.2.2) := Primrec.snd.comp Primrec.snd
  have step : Primrec (fun p : Step => if p.2.1 = p.1.1 then true else p.2.2) :=
    Primrec.ite (Primrec.eq.comp next rank) (Primrec.const true) acc
  have ranks : Primrec (Prod.snd : Args → List Nat) := Primrec.snd
  exact (Primrec.list_foldr ranks (Primrec.const false) step.to₂).to₂

private theorem recordRankPrimitive : Primrec₂ recordRank := by
  have check : PrimrecPred (fun p : Nat × List Nat => rankPresent p.1 p.2 = true) :=
    Primrec.eq.comp rankPresentPrimitive (Primrec.const true)
  exact Primrec.ite check Primrec.snd (Primrec.list_cons.comp Primrec.fst Primrec.snd)

private theorem rankSupportPrimitive : Primrec rankSupportCode := by
  let Step := List WeightedCode × (WeightedCode × List Nat)
  have term : Primrec (fun p : Step => p.2.1) := Primrec.fst.comp Primrec.snd
  have rank : Primrec (fun p : Step => p.2.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp term))
  have acc : Primrec (fun p : Step => p.2.2) := Primrec.snd.comp Primrec.snd
  have step := recordRankPrimitive.comp rank acc
  exact Primrec.list_foldr Primrec.id (Primrec.const []) step.to₂

private theorem lookupPrimitive : Primrec₂ lookup := by
  let Args := Nat × Residues
  let Step := Args × ((Nat × Nat) × Nat)
  have rank : Primrec (fun p : Step => p.1.1) := Primrec.fst.comp Primrec.fst
  have entry : Primrec (fun p : Step => p.2.1) := Primrec.fst.comp Primrec.snd
  have acc : Primrec (fun p : Step => p.2.2) := Primrec.snd.comp Primrec.snd
  have step : Primrec (fun p : Step => if p.2.1.1 = p.1.1 then p.2.1.2 else p.2.2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp entry) rank) (Primrec.snd.comp entry) acc
  have entries : Primrec (Prod.snd : Args → Residues) := Primrec.snd
  exact (Primrec.list_foldr entries (Primrec.const 0) step.to₂).to₂

private theorem residueVectorPrimitive : Primrec₂ residueVectorCode := by
  let Args := List WeightedCode × Residues
  let Step := Args × (WeightedCode × Int)
  have term : Primrec (fun p : Step => p.2.1) := Primrec.fst.comp Primrec.snd
  have entries : Primrec (fun p : Step => p.1.2) := Primrec.snd.comp Primrec.fst
  have rank : Primrec (fun p : Step => p.2.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp term))
  have single := Primrec.list_cons.comp term (Primrec.const [])
  have read := lookupPrimitive.comp rank entries
  have addend := fixed_mixedSameRankResidueCodeExact.1.comp single read
  have acc : Primrec (fun p : Step => p.2.2) := Primrec.snd.comp Primrec.snd
  have step := add_primitive.comp addend acc
  have terms : Primrec (Prod.fst : Args → List WeightedCode) := Primrec.fst
  exact (Primrec.list_foldr terms (Primrec.const (0 : Int)) step.to₂).to₂

private theorem rankCode (t : WeightedOperand) : (encodeWeighted t).2.2.1 = t.2.rank := by
  rcases t with ⟨weight,op⟩
  cases op <;> rfl

private theorem rankSupportLiteral (terms : List WeightedOperand) :
    rankSupportCode (terms.map encodeWeighted) = rankSupport terms := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    change recordRank (encodeWeighted t).2.2.1 (rankSupportCode (ts.map encodeWeighted)) =
      recordRank t.2.rank (rankSupport ts)
    rw [rankCode,ih]

private theorem residueVectorLiteral (terms : List WeightedOperand) (entries : Residues) :
    residueVectorCode (terms.map encodeWeighted) entries = residueVector terms entries := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    change weightedResidueCode ([t].map encodeWeighted) (lookup (encodeWeighted t).2.2.1 entries) +
      residueVectorCode (ts.map encodeWeighted) entries =
      weightedResidue [t] (lookup t.2.rank entries) + residueVector ts entries
    rw [rankCode,fixed_mixedSameRankResidueCodeExact.2.2.1,ih]

theorem codeExact : CodeExact :=
  ⟨rankSupportPrimitive,residueVectorPrimitive,rankSupportLiteral,residueVectorLiteral⟩

end LogicLineages.PermittedControl.MixedRankResidue
