import LogicLineages.PersistentMarking.NumberedWindowSimulationPlacement

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationSourceSplitProof
open NumberedWindowSyntax NumberedWindowTupleTargets
open NumberedWindowSimulationJobs NumberedWindowSimulationPlacement
open NumberedWindowOrdinaryTranslation

theorem rightAll (qs : Spine.Args) : Spine.Split qs .nil qs := by
  cases qs with
  | nil => exact .nil
  | cons q qs => exact .right (rightAll qs)
termination_by sizeOf qs

theorem removeAsSplit {qs q rest} (h : Spine.Remove qs q rest) :
    Spine.Split qs (.cons q .nil) rest := by
  induction h with
  | here => exact .left (rightAll _)
  | there _ ih => exact .right ih

theorem realizedSplit {qs ls rs} (h : Spine.Split qs ls rs) (n : Nat) :
    ∀ As, RealizesArgs n qs As → ∃ L R, RealizesArgs n ls L ∧ RealizesArgs n rs R ∧
      As.toList.Perm (L.toList ++ R.toList) := by
  induction h with
  | nil =>
    intro As hA
    cases hA
    exact ⟨.nil,.nil,.nil,.nil,.nil⟩
  | left _ ih =>
    intro As hA
    cases hA with
    | cons hq ht =>
      obtain ⟨L,R,hL,hR,hp⟩ := ih _ ht
      exact ⟨.cons _ L,R,.cons hq hL,hR,.cons _ hp⟩
  | right _ ih =>
    intro As hA
    cases hA with
    | cons hq ht =>
      obtain ⟨L,R,hL,hR,hp⟩ := ih _ ht
      exact ⟨L,.cons _ R,hL,.cons hq hR,(List.Perm.cons _ hp).trans List.perm_middle.symm⟩

theorem realizedNonempty {n qs As} (h : RealizesArgs n qs As) (hn : Spine.Nonempty qs) :
    As.toList ≠ [] := by
  cases h with
  | nil => exact hn.elim
  | cons hq ht => intro h; cases h

private theorem someLeft {ts ls rs : Spine.Args} {t : Spine.Expr}
    (ih : ∀ L R, trArgs ls = some L → trArgs rs = some R →
      ∃ p : Place (types ls) (types rs) (types ts), trArgs ts = some (weave p L R)) :
    ∀ L R, trArgs (.cons t ls) = some L → trArgs rs = some R →
      ∃ p : Place (types (.cons t ls)) (types rs) (types (.cons t ts)),
        trArgs (.cons t ts) = some (weave p L R) := by
  intro L R hl hr
  cases hq : tr t with
  | none => simp [trArgs,hq] at hl
  | some Q =>
    cases hls : trArgs ls with
    | none => simp [trArgs,hq,hls] at hl
    | some L' =>
      have he : NArgs.cons Q L' = L := by simpa [trArgs,hq,hls] using hl
      subst L
      obtain ⟨p,hp⟩ := ih L' R hls hr
      exact ⟨.left p,by simp [trArgs,hq,hp,weave]⟩

private theorem someRight {ts ls rs : Spine.Args} {t : Spine.Expr}
    (ih : ∀ L R, trArgs ls = some L → trArgs rs = some R →
      ∃ p : Place (types ls) (types rs) (types ts), trArgs ts = some (weave p L R)) :
    ∀ L R, trArgs ls = some L → trArgs (.cons t rs) = some R →
      ∃ p : Place (types ls) (types (.cons t rs)) (types (.cons t ts)),
        trArgs (.cons t ts) = some (weave p L R) := by
  intro L R hl hr
  cases hq : tr t with
  | none => simp [trArgs,hq] at hr
  | some Q =>
    cases hrs : trArgs rs with
    | none => simp [trArgs,hq,hrs] at hr
    | some R' =>
      have he : NArgs.cons Q R' = R := by simpa [trArgs,hq,hrs] using hr
      subst R
      obtain ⟨p,hp⟩ := ih L R' hl hrs
      exact ⟨.right p,by simp [trArgs,hq,hp,weave]⟩

theorem quotedPlacement {ts ls rs} (h : Spine.Split ts ls rs) :
    ∀ L R, trArgs ls = some L → trArgs rs = some R →
      ∃ p : Place (types ls) (types rs) (types ts), trArgs ts = some (weave p L R) := by
  induction h with
  | nil => intro L R hl hr; exact ⟨.nil,rfl⟩
  | left _ ih => exact someLeft ih
  | right _ ih => exact someRight ih

end LogicLineages.PersistentMarking.NumberedWindowSimulationSourceSplitProof
