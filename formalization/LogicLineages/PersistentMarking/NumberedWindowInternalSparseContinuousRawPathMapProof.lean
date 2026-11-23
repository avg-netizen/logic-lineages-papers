module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseContinuousRawRowsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFixedArgumentClassHopProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMappedRawPathJoinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenGateProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenCallsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseContinuousRawPathMapProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph5Rename)
open NumberedWindowInternalSparsePathAdvanceOpenGateProof (recoverGate)
open NumberedWindowInternalSparsePathAdvanceOpenCallsProof (callsRead)
open NumberedWindowInternalSparseContinuousRawRowsProof (Row Rows)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow)
open NumberedWindowInternalCoverCombinedRestrictedFormationTargets (thinFormation)
open NumberedWindowInternalSparseFixedArgumentClassHopProof (classHopCases)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseAddressSingletonTargets (singletonCertificate)
open NumberedWindowInternalSparseMappedRawPathReportProof (mapped mappedRename provide)
open NumberedWindowInternalSparseMappedRawPathJoinProof (prepend)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem rowStep {β : Type} {Δ : List (Formula β)} (raw : Program 5) (least : Program 3)
    (ctx dom cod src q cert tail dst r : OTerm α)
    (row : Row body Γ raw least ctx (rawCons dom cod) src q cert tail dst r)
    (ρ : α → β) (hρ : ∀ p ∈ Γ, p.relabel ρ ∈ Δ) :
    ∃ witness : OTerm β, Nonempty (Derivation body Δ
      (programGraph raw (suc z)
        ![ctx.relabel ρ,rawCons (dom.relabel ρ) (cod.relabel ρ),q.relabel ρ,witness,r.relabel ρ])) := by
  obtain ⟨head,witness,_,live,owned⟩ := row.witnesses
  obtain ⟨gate⟩ := recoverGate raw least ctx (rawCons dom cod) (suc src) head dst live
  obtain ⟨values⟩ := callsRead raw least ctx (rawCons dom cod) src head dst q witness r owned
    ⟨Derivation.conjunctionLeft gate⟩
  have v := renameInto ⟨Derivation.conjunctionLeft values⟩ ρ Δ hρ
  rw [graph5Rename,rawConsRename,sucRelabel,zRelabel] at v
  exact ⟨witness.relabel ρ,v⟩

private theorem one (C root other baseW : Program 3) (X : Program 2) (s : Settings) (V : Program 1)
    (ctx dom cod arg q w r : OTerm α) :
    let W := thinMatchingWindow C s baseW V
    let raw := typedRaw5 root other W V
    let least := packedLeastProgram C X W s
    let l := auxiliaryTerm dom cod q arg
    let y := auxiliaryTerm dom cod r arg
    Nonempty (Derivation body Γ (thinFormation W ctx dom cod arg)) →
    Nonempty (Derivation body Γ (programGraph raw (suc z) ![ctx,rawCons dom cod,q,w,r])) →
    Nonempty (Derivation body Γ (mapped raw least ctx cod l y)) := by
  intro W raw least l y held live
  apply classHopCases C root other baseW X s V ctx dom cod arg q w r _ held live
  intro β j Δ a b leftAux rightAux keep lcall rcall cert
  rw [mappedRename,auxiliaryRename,auxiliaryRename]
  obtain ⟨vL⟩ := lcall
  obtain ⟨vR⟩ := rcall
  obtain ⟨vC⟩ := cert
  exact provide raw least (ctx.relabel j) (cod.relabel j) leftAux rightAux a b
    (singletonCertificate b leftAux (functionWitnessTerm (w.relabel j)) rightAux)
    ⟨Derivation.conjunctionIntroduction vL (Derivation.conjunctionIntroduction vR vC)⟩

private theorem extend (C root other baseW : Program 3) (X : Program 2) (s : Settings) (V : Program 1)
    (ctx dom cod arg q w r last : OTerm α) :
    let W := thinMatchingWindow C s baseW V
    let raw := typedRaw5 root other W V
    let least := packedLeastProgram C X W s
    let l := auxiliaryTerm dom cod q arg
    let m := auxiliaryTerm dom cod r arg
    let y := auxiliaryTerm dom cod last arg
    Nonempty (Derivation body Γ (thinFormation W ctx dom cod arg)) →
    Nonempty (Derivation body Γ (programGraph raw (suc z) ![ctx,rawCons dom cod,q,w,r])) →
    Nonempty (Derivation body Γ (mapped raw least ctx cod m y)) →
    Nonempty (Derivation body Γ (mapped raw least ctx cod l y)) := by
  intro W raw least l m y held live rest
  apply classHopCases C root other baseW X s V ctx dom cod arg q w r _ held live
  intro β j Δ a b leftAux rightAux keep lcall rcall cert
  have tail := renameInto rest j Δ keep
  rw [mappedRename] at tail
  have h : Nonempty (Derivation body Δ (mapped raw least (ctx.relabel j) (cod.relabel j)
      rightAux (y.relabel j))) := by
    simpa only [m,rightAux,auxiliaryRename] using tail
  rw [mappedRename,auxiliaryRename]
  exact prepend C X W s raw (ctx.relabel j) (dom.relabel j) (cod.relabel j)
    (arg.relabel j) leftAux (r.relabel j) (y.relabel j) a b
    (singletonCertificate b leftAux (functionWitnessTerm (w.relabel j)) rightAux)
    lcall rcall cert h

/-- Map a genuinely nonempty finite directed source tape with literal raw
continuity on the fixed actual raw argument. All result and certificate
witnesses are supplied by the object derivation, not externally assumed.
The stronger across-representative continuation is deliberately absent. -/
theorem mapRows (C root other baseW : Program 3) (X : Program 2) (s : Settings) (V : Program 1)
    (ctx dom cod arg src q cert dst r : OTerm α)
    (path : Rows body Γ
      (typedRaw5 root other (thinMatchingWindow C s baseW V) V)
      (packedLeastProgram C X (thinMatchingWindow C s baseW V) s)
      ctx (rawCons dom cod) src q cert dst r) :
    ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (thinFormation (thinMatchingWindow C s baseW V)
        (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j))) →
      Nonempty (Derivation body Δ
        (mapped (typedRaw5 root other (thinMatchingWindow C s baseW V) V)
          (packedLeastProgram C X (thinMatchingWindow C s baseW V) s) (ctx.relabel j) (cod.relabel j)
          (auxiliaryTerm (dom.relabel j) (cod.relabel j) (q.relabel j) (arg.relabel j))
          (auxiliaryTerm (dom.relabel j) (cod.relabel j) (r.relabel j) (arg.relabel j)))) := by
  let W := thinMatchingWindow C s baseW V
  let raw := typedRaw5 root other W V
  let least := packedLeastProgram C X W s
  induction path with
  | @last source left code target right row =>
    intro β j Δ keep form
    obtain ⟨w,h⟩ := rowStep raw least ctx dom cod source left code z target right row j keep
    exact one C root other baseW X s V (ctx.relabel j) (dom.relabel j) (cod.relabel j)
      (arg.relabel j) (left.relabel j) w (right.relabel j) form h
  | @cons source left code tail middle midRaw target right row rest ih =>
    intro β j Δ keep form
    obtain ⟨w,h⟩ := rowStep raw least ctx dom cod source left code tail middle midRaw row j keep
    have suffix := ih β j Δ keep form
    exact extend C root other baseW X s V (ctx.relabel j) (dom.relabel j) (cod.relabel j)
      (arg.relabel j) (left.relabel j) w (midRaw.relabel j) (right.relabel j) form h suffix

#print axioms mapRows
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseContinuousRawPathMapProof
