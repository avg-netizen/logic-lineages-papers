module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationValidityStackAppend (append)
open TwoSol20261113.CalibratedPrimary.Membership
open Preservation PreservationSyntaxProof PreservationBindingProof PreservationCoreProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem inductionStep (raw : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (AtRaw raw)) := by
  apply atRawIntro raw
  let suffix : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let out : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let needle : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let A := fields (raw.relabel Sum.inl) suffix out needle
  have hb' := renameInto hb (Sum.inl : alpha → alpha ⊕ Fin 3)
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [belowRawRename] at hb'
  have ha : Nonempty (Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl))
      (graph2 append out (raw.relabel Sum.inl) suffix)) :=
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  have hm : Nonempty (Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl))
      (graph2 contains (suc z) (raw.relabel Sum.inl) needle)) :=
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨h⟩ := core (raw.relabel Sum.inl) suffix out needle (withHyp hb' A) ha hm
  exact ⟨Derivation.implicationIntroduction h⟩

theorem appendPreservation (raw suffix out needle : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 append out raw suffix)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) raw needle))) :
    Nonempty (Derivation body Delta (graph2 contains (suc z) out needle)) :=
  atRawApply raw suffix out needle
    (rawInduction raw (fun _ _ r hb => inductionStep r hb)) (andIntro ha hm)

theorem internalPreservation : Targets.InternalPreservation := by
  intro E body alpha Delta pool reached parameter out needle he hm
  let xs : Fin 3 → OTerm alpha := ![pool,reached,parameter]
  apply programCases (filterReached E) xs _
  intro beta j Theta filtered hj hf
  simp only [graph2Rename,sucRelabel,zRelabel]
  have he' := renameInto he j Theta hj
  rw [graph3Rename] at he'
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hm'
  let ys : Fin 3 → OTerm beta := ![pool.relabel j,reached.relabel j,parameter.relabel j]
  have hf' : Nonempty (Derivation body Theta (programGraph (filterReached E) filtered ys)) := hf
  have ha := binaryRecover append (.projection 1) (filterReached E) (out.relabel j)
    (reached.relabel j) filtered ys he' (projectionValue 1 ys) hf'
  exact appendPreservation (reached.relabel j) filtered (out.relabel j) (needle.relabel j) ha hm'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationProof
