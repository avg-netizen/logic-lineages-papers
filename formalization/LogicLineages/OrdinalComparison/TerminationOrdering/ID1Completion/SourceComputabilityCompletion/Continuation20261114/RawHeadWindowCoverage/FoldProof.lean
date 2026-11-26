module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.FoldCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.FoldProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Fold FoldSyntaxProof FoldBindingProof FoldCoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)} {k : Nat}
variable (base : Program k) (step : Program (k+2)) (transform : Program (k+1))
variable (hit : Hit body step transform) (keep : Tail body step)
include hit keep

theorem inductionStep (raw : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw base step transform raw))) :
    Nonempty (Derivation body Delta (AtRaw base step transform raw)) := by
  apply atRawIntro base step transform raw
  let needle : OTerm (alpha ⊕ Fin (k+3)) := .var (.inr 0)
  let image : OTerm (alpha ⊕ Fin (k+3)) := .var (.inr 1)
  let out : OTerm (alpha ⊕ Fin (k+3)) := .var (.inr 2)
  let params : Fin k → OTerm (alpha ⊕ Fin (k+3)) := fun i => .var (.inr i.succ.succ.succ)
  let A := fields base step transform (raw.relabel Sum.inl) needle image out params
  have hb' := renameInto hb (Sum.inl : alpha → alpha ⊕ Fin (k+3))
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [belowRawRename] at hb'
  have hh : Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl)) A :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨h⟩ := core base step transform hit keep (raw.relabel Sum.inl) needle image out params (withHyp hb' A)
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hh)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight hh)⟩ ⟨Derivation.conjunctionLeft hh⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem coverage (raw needle image out : OTerm alpha) (params : Fin k → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph transform image (Fin.cons needle params))))
    (hm : Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains
      (SourceComputabilityFormulaSupportProof.numeral 1) raw needle)))
    (hf : Nonempty (Derivation body Delta (programGraph (InternalRawListRecursion.listRec base step) out (Fin.cons raw params)))) :
    Nonempty (Derivation body Delta (result out image)) :=
  atRawApply base step transform raw needle image out params
    (rawInduction base step transform raw (fun _ _ r hb => inductionStep base step transform hit keep r hb))
    (andIntro hf (andIntro ht hm))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.FoldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.FoldProof
