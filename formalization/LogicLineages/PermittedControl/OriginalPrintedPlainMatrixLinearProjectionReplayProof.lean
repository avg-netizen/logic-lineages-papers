module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionTargets
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionTransportProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesEnumerateProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesGuardProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesRealizationProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjection
open ActualFiniteOrderBranches (Entry guard rename realized exactPatternEnumeration exactOrderGuard exactBranchRealization)
open OriginalPrintedPlainMatrixInfiniteLow (matrix)
open OriginalMatrixDenseRanks (support)
open OriginalMatrixActualHighPacket (originalFamilyCeiling)

theorem exactGreatestReplayGuards : ExactGreatestReplayGuards := by
  intro B θ known gates p branch member checked z high
  let names := support (matrix known gates p)
  let ρ := realized θ branch
  let later := Function.update ρ (top branch) z
  let replayed := replay θ known gates p branch z
  obtain ⟨_,keys,bounds,_⟩ := (exactPatternEnumeration names branch).mp member
  obtain ⟨strict,slots,_⟩ := exactBranchRealization θ names branch member checked
  have value (e : Entry) (he : e ∈ branch.2) : replayed e.1 = later e.2 := by
    have used : e.1 ∈ names := by
      rw [← keys]
      exact List.mem_map.mpr ⟨e,he,rfl⟩
    have tied := updatedTies θ known gates p branch member checked z e.1 used
    change later (rename branch e.1) = replayed e.1 at tied
    rw [(slots e he).1] at tied
    exact tied.symm
  have sorted (i j : Nat) (hij : i < j) (hj : j < branch.1) : later i < later j := by
    have hjTop : j ≤ top branch := by
      change j ≤ branch.1 - 1
      omega
    by_cases eq : j = top branch
    · have hi : i < top branch := hij.trans_le hjTop
      have nz : top branch ≠ 0 := by omega
      have pay : ρ (top branch-1) + 1 ≤ z := by
        have rhs : (if top branch = 0 then 0 else ρ (top branch-1)+1) ≤ z :=
          (le_max_right _ _).trans high
        simpa only [if_neg nz] using rhs
      have idx : i ≤ top branch - 1 := by omega
      change Function.update ρ (top branch) z i < Function.update ρ (top branch) z j
      rw [Function.update_of_ne (ne_of_lt hi),eq,Function.update_self]
      exact (strict.monotone idx).trans_lt (Nat.lt_of_succ_le pay)
    · have hi : i ≠ top branch := ne_of_lt (hij.trans_le hjTop)
      change Function.update ρ (top branch) z i < Function.update ρ (top branch) z j
      rw [Function.update_of_ne hi,Function.update_of_ne eq]
      exact strict hij
  refine ⟨(exactOrderGuard replayed branch).mpr ?_,?_⟩
  · intro a ha b hb
    rw [value a ha,value b hb]
    exact ⟨fun h => congrArg later h,fun lt => sorted a.2 b.2 lt (bounds b hb)⟩
  · intro paid name used
    have zPaid : originalFamilyCeiling B known gates p ≤ z := (le_max_left _ _).trans high
    by_cases hTop : rename branch name = top branch
    · simpa only [replay,if_pos (And.intro used hTop)] using zPaid
    · have lower : ¬ (name ∈ support (matrix known gates p) ∧ rename branch name = top branch) :=
        fun h => hTop h.2
      simpa only [replay,if_neg lower] using paid name used

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjection
