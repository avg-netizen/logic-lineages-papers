module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixResidualClosureTargets
import LogicLineages.PermittedControl.OriginalProjectedMatrixDecodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixResidualClosure
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalMatrixLowDimension (supportSet)
open OriginalPrintedPlainMatrixProjectedSupport (argumentNames)
open OriginalProjectedMatrixDecode (Summand decode LiteralTerm LiteralRow exactProjectedMatrixDecode)
open OriginalProjectedMatrixSemantics (availableRow availabilityRows)
open OriginalMatrixDenseRanks (support)
open HeterogeneousSignedMatrixSlice (Row)
open MixedSameRankResidue (WeightedOperand)
open PreparedProjection (LowerOperand)

private theorem termOrigin (ops : List LowerOperand) {source : List Summand} {out : List WeightedOperand}
    (literal : List.Forall₂ (LiteralTerm ops) source out) :
    ∀ t ∈ out, t.2 ∈ ops := by
  induction literal with
  | nil => intro t empty; cases empty
  | @cons s q ss qs head tail ih =>
      intro t member
      rcases List.mem_cons.mp member with equal | later
      · subst t
        obtain ⟨j,hj,_,eq⟩ := head
        rw [eq]
        exact List.getElem_mem hj
      · exact ih t later

private theorem rowOrigin (ops : List LowerOperand) {source : List NormalForm.Atom} {out : List Row}
    (literal : List.Forall₂ (LiteralRow ops) source out) :
    ∀ row ∈ out, ∀ t ∈ row.2.2, t.2 ∈ ops := by
  induction literal with
  | nil => intro r empty; cases empty
  | @cons a r atoms rows head tail ih =>
      intro q hq
      rcases List.mem_cons.mp hq with equal | later
      · subst q
        exact termOrigin ops head.2.2
      · exact ih q later

theorem residualArgumentNames (ops : List LowerOperand) (p : NormalForm.Formula) (rows : List Row)
    (decoded : decode ops p = some rows) :
    supportSet (availabilityRows ops ++ rows) = argumentNames ops := by
  have literals := (exactProjectedMatrixDecode.2.1 ops p rows).mp decoded
  apply Finset.ext
  intro name
  constructor
  · intro member
    obtain ⟨row,atRow,hasName⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp member)
    obtain ⟨t,atTerm,hasRank⟩ := List.mem_map.mp hasName
    have source : t.2 ∈ ops := by
      rcases List.mem_append.mp atRow with guardRow | projectedRow
      · obtain ⟨op,used,rfl⟩ := List.mem_map.mp guardRow
        have only : t = (1,op) := List.mem_singleton.mp atTerm
        rw [only]
        exact used
      · exact rowOrigin ops literals row projectedRow t atTerm
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨t.2,source,hasRank⟩)
  · intro member
    obtain ⟨op,used,rank⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    have guardRow : availableRow op ∈ availabilityRows ops := List.mem_map.mpr ⟨op,used,rfl⟩
    exact List.mem_toFinset.mpr (List.mem_flatMap.mpr
      ⟨availableRow op,List.mem_append_left _ guardRow,List.mem_map.mpr ⟨(1,op),List.mem_cons_self,rank⟩⟩)

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixResidualClosure
