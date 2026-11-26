module
public import LogicLineages.PermittedControl.StageEmitterHighTargets
import LogicLineages.PermittedControl.StageEmitterRowProof
import LogicLineages.PermittedControl.RawPacketAlgebraJoinEffectivityProof
import LogicLineages.PermittedControl.RawPacketAlgebraChildProof
import LogicLineages.PermittedControl.RawProperClauseProof
import LogicLineages.PermittedControl.ActualBitFamilyRawRankPrimitiveProof
import LogicLineages.PermittedControl.ActualBitFamilyRawChartsPrimitiveProof
import Mathlib.Computability.Primrec.List

public section
namespace LogicLineages.PermittedControl.StageEmitter
open PreparedProjection (PreparedPacketCode)
open StageCallbackRawLevel (Rendering rowCode)
open RawPacketAlgebra (childCode joinCode joinEffectivity childEffectivity)
open RawProperClause (properClausesCode exactRawProperClauseEffectivity)
open ActualBitFamilyRawRank (familyCode exactRawRankEffectivity)
open ActualBitFamilyRawCharts (exactRawChartEffectivity)
open ActualBitFamilyRawLayout (RawFamily RawBitRow)
open ActualFiniteOrderBranches (Pattern)
open OriginalPrintedPlainMatrixLinearProjection (top)

private theorem topPrimitive : Primrec (fun p : Pattern => top p) := by
  have h := Primrec.nat_sub.comp (Primrec.fst : Primrec (fun p : Pattern => p.1)) (Primrec.const 1)
  exact h

section
variable (R : Rendering) (hR : RenderingEffective R)
include hR

private theorem chartPrimitive :
    Primrec (fun y : (Nat × RawFamily) × Pattern => chartCode R y.1.1 y.1.2 y.2) := by
  let Y := (Nat × RawFamily) × Pattern
  have cut : Primrec (fun y : Y => y.1.1) := Primrec.fst.comp Primrec.fst
  have raw : Primrec (fun y : Y => y.1.2) := Primrec.snd.comp Primrec.fst
  have pat : Primrec (fun y : Y => y.2) := Primrec.snd
  have width : Primrec (fun y : Y => y.2.1) := Primrec.fst.comp pat
  have tp : Primrec (fun y : Y => top y.2) := topPrimitive.comp pat
  have famArgs : Primrec (fun y : Y => (y.2,y.1.2)) := pat.pair raw
  have fam : Primrec (fun y : Y => familyCode (y.2,y.1.2)) := by
    have h := exactRawRankEffectivity.2.comp famArgs
    exact h
  have kept : Primrec (fun y : Y => properClausesCode (familyCode (y.2,y.1.2))) := by
    have h := exactRawProperClauseEffectivity.2.2.2.2.2.1.comp fam
    exact h
  have rowArgs : Primrec (fun z : (Y × List RawBitRow) × RawBitRow => (z.1.1.2.1,top z.1.1.2,z.2)) :=
    ((width.comp Primrec.fst).comp Primrec.fst).pair (((tp.comp Primrec.fst).comp Primrec.fst).pair Primrec.snd)
  have row : Primrec (fun z : (Y × List RawBitRow) × RawBitRow => rowCode R z.1.1.2.1 (top z.1.1.2) z.2) := by
    have h := (exactRowCodeEffectivity R hR).comp rowArgs
    exact h
  have mapped : Primrec (fun z : Y × List RawBitRow => z.2.map (rowCode R z.1.2.1 (top z.1.2))) :=
    Primrec.list_map Primrec.snd row.to₂
  have joined : Primrec (fun z : Y × List RawBitRow => joinCode (z.2.map (rowCode R z.1.2.1 (top z.1.2)))) := by
    have h := joinEffectivity.2.2.2.2.comp mapped
    exact h
  have flat : Primrec (fun y : Y => (properClausesCode (familyCode (y.2,y.1.2))).flatMap
      (fun rows => joinCode (rows.map (rowCode R y.2.1 (top y.2))))) :=
    Primrec.list_flatMap kept joined.to₂
  have childArgs : Primrec (fun y : Y => (y.1.1,top y.2,(properClausesCode (familyCode (y.2,y.1.2))).flatMap
      (fun rows => joinCode (rows.map (rowCode R y.2.1 (top y.2)))))) :=
    cut.pair (tp.pair flat)
  have h := childEffectivity.1.comp childArgs
  exact h

private theorem highPrimitive : Primrec (highCode R) := by
  have charts : Primrec (fun x : Nat × RawFamily => ActualBitFamilyRawCharts.charts x.2) := by
    have h := exactRawChartEffectivity.2.2.2.2.comp (Primrec.snd : Primrec (fun x : Nat × RawFamily => x.2))
    exact h
  have h := Primrec.list_map charts (chartPrimitive R hR).to₂
  exact h.of_eq (fun x => rfl)

end

theorem exactHighCodeEffectivity : ExactHighCodeEffectivity :=
  fun R hR => ⟨highPrimitive R hR,(highPrimitive R hR).to_comp⟩

#print axioms exactHighCodeEffectivity
end LogicLineages.PermittedControl.StageEmitter
