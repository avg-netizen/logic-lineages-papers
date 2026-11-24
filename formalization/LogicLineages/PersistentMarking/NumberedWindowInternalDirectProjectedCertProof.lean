module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectProjectedCertTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectProjectedCertSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapOriginProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapOriginSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeMemberProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectProjectedCert
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open NumberedWindowInternalDirectProjectedCertTargets
open NumberedWindowInternalDirectProjectedCertSyntaxProof (renameShared pinTarget)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough)
open NumberedWindowInternalDirectTargetMapOriginTargets (origin originBody originRow)
open NumberedWindowInternalDirectTargetMapOriginSyntaxProof (rowRename)
open NumberedWindowInternalDirectTargetMapOrigin (exactOpenProjectedTargetOrigin)
open NumberedWindowInternalDirectSharedTapeMember (exactOpenSharedTapeMember)

theorem exactProjectedCert : ExactProjectedCert := by
  intro q v r B α Γ src dst kept removed inserted s t k d a p sk tp key goal shared member next
  obtain ⟨cut⟩ := exactOpenProjectedTargetOrigin B α Γ a p key
  obtain ⟨actual⟩ := shared.scratchProjection
  obtain ⟨m⟩ := member
  have root : Derivation B Γ (origin a key) :=
    Derivation.implicationElimination cut (Derivation.conjunctionIntroduction actual m)
  let φ := originBody a key
  let i : α → α ⊕ Fin 1 := Sum.inl
  let Δ := φ :: Γ.map (fun f => f.relabel i)
  let row : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  have keep : ∀ f ∈ Γ, f.relabel i ∈ Δ := by
    intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have report : Derivation B Δ (originRow (a.relabel i) (key.relabel i) row) :=
    Derivation.hypothesis List.mem_cons_self
  have here := renameShared q v r src dst kept removed inserted s t k d a p sk tp shared i keep
  have inside : Nonempty (Derivation B Δ (goal.relabel i)) := by
    apply exactOpenSharedTapeMember q v r B (α ⊕ Fin 1) Δ
      (src.relabel i) (dst.relabel i) (kept.relabel i) (removed.relabel i) (inserted.relabel i)
      (s.relabel i) (t.relabel i) (k.relabel i) (d.relabel i) (a.relabel i) (p.relabel i)
      (sk.relabel i) (tp.relabel i) row (goal.relabel i) here ⟨Derivation.conjunctionLeft report⟩
    intro β j Ω old dom cert retain got
    let ρ := j ∘ i
    have opened := renameInto (show Nonempty (Derivation B Δ (originRow
      (a.relabel i) (key.relabel i) row)) from ⟨report⟩) j Ω retain
    rw [rowRename,Term.relabel_relabel,Term.relabel_relabel] at opened
    obtain ⟨found⟩ := opened
    have graphs := Derivation.conjunctionRight found
    have pinned := pinTarget r ((removed.relabel i).relabel j) (row.relabel j)
      ((d.relabel i).relabel j) old (key.relabel ρ) dom cert got
      ⟨Derivation.conjunctionLeft graphs⟩ ⟨Derivation.conjunctionRight graphs⟩
    rw [formulaRelabelComposition]
    apply next β ρ Ω (row.relabel j) dom cert (keepThrough i j keep retain) ⟨found⟩
    simpa only [ρ,Term.relabel_relabel] using pinned
  obtain ⟨out⟩ := inside
  exact ⟨Derivation.existentialElimination root out⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectProjectedCert
