module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionCompositionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalControlGraphSupportProof (valueUnique headTransport)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (tailMember)
open NumberedWindowInternalSparseDirectedSeen (scanGraph)
open NumberedWindowInternalSparseDirectedFilter (cell passGraph restRow restReport filterStep)
open NumberedWindowInternalSparseDirectedFilterOpenSyntaxProof (reportBinder)
open NumberedWindowInternalSparseDirectedFilterOpenChecks (exact_OpenDirectedFilterCons)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof
  (hitGraph included includedRename missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion headHit)
open NumberedWindowInternalSparseFilterInclusionCompositionProof (hitIntro hitCases)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Occurrence in the genuine filtered tail: the inductive hypothesis at
the real tail, then the checked tail membership introduction. -/
private theorem fromTail (E : Program 4) (code h tail seen ctx ty k rest : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (inherited : Nonempty (Derivation body Γ (included E tail seen ctx ty k)))
    (tailRun : Nonempty (Derivation body Γ (passGraph E rest tail seen ctx ty)))
    (member : Nonempty (Derivation body Γ (memberGraph rest k))) :
    Nonempty (Derivation body Γ (memberGraph code k)) := by
  obtain ⟨hit⟩ := hitIntro E rest tail seen ctx ty k tailRun member
  obtain ⟨ih⟩ := inherited
  exact tailMember code h tail k input ⟨Derivation.implicationElimination ih hit⟩

/-- Retained head: the output is the literal cons of the same head onto
the genuine filtered tail. Invert membership at that actual output cons. -/
private theorem retained (E : Program 4) (code h tail seen ctx ty k out rest : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (inherited : Nonempty (Derivation body Γ (included E tail seen ctx ty k)))
    (tailRun : Nonempty (Derivation body Γ (passGraph E rest tail seen ctx ty)))
    (built : Nonempty (Derivation body Γ (cell out h rest)))
    (member : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (memberGraph code k)) := by
  let A := (missGraph h k).not
  let B := memberGraph rest k
  obtain ⟨split⟩ := consInversion out h rest k built member
  obtain ⟨c⟩ := input
  obtain ⟨ih⟩ := inherited
  obtain ⟨run⟩ := tailRun
  obtain ⟨left⟩ := headHit (body := body) (Γ := A :: Γ) code h tail k
    ⟨addHyp c A⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨right⟩ := fromTail (body := body) (Γ := B :: Γ) E code h tail seen ctx ty k rest
    ⟨addHyp c B⟩ ⟨addHyp ih B⟩ ⟨addHyp run B⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination split
    (Derivation.implicationIntroduction left) (Derivation.implicationIntroduction right)⟩

/-- Skipped head: the output is the genuine filtered tail itself. -/
private theorem skipped (E : Program 4) (code h tail seen ctx ty k out rest : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (inherited : Nonempty (Derivation body Γ (included E tail seen ctx ty k)))
    (tailRun : Nonempty (Derivation body Γ (passGraph E rest tail seen ctx ty)))
    (same : Nonempty (Derivation body Γ (eqn out rest)))
    (member : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (memberGraph code k)) := by
  have moved : Nonempty (Derivation body Γ (memberGraph rest k)) :=
    headTransport scratchMember (suc z) out rest (![k] : Fin 1 → OTerm α) same member
  exact fromTail E code h tail seen ctx ty k rest input inherited tailRun moved

/-- Both physical alternatives of the checked filter row share one
genuine result of the same pass on the real tail. -/
private theorem withRow (E : Program 4) (code h tail seen ctx ty k out rest : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (inherited : Nonempty (Derivation body Γ (included E tail seen ctx ty k)))
    (member : Nonempty (Derivation body Γ (memberGraph out k)))
    (row : Nonempty (Derivation body Γ (restRow E out h tail rest seen ctx ty))) :
    Nonempty (Derivation body Γ (memberGraph code k)) := by
  let L : Formula α := scanGraph E seen ctx ty h ⊓ cell out h rest
  let R : Formula α := (scanGraph E seen ctx ty h).not ⊓ eqn out rest
  obtain ⟨row⟩ := row
  obtain ⟨c⟩ := input
  obtain ⟨ih⟩ := inherited
  obtain ⟨m⟩ := member
  have run : Derivation body Γ (passGraph E rest tail seen ctx ty) :=
    Derivation.conjunctionLeft row
  have alternatives : Derivation body Γ (L ⊔ R) := Derivation.conjunctionRight row
  have hl : Derivation body (L :: Γ) (scanGraph E seen ctx ty h ⊓ cell out h rest) :=
    Derivation.hypothesis List.mem_cons_self
  have hr : Derivation body (R :: Γ) ((scanGraph E seen ctx ty h).not ⊓ eqn out rest) :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨left⟩ := retained (body := body) (Γ := L :: Γ) E code h tail seen ctx ty k out rest
    ⟨addHyp c L⟩ ⟨addHyp ih L⟩ ⟨addHyp run L⟩ ⟨Derivation.conjunctionRight hl⟩ ⟨addHyp m L⟩
  obtain ⟨right⟩ := skipped (body := body) (Γ := R :: Γ) E code h tail seen ctx ty k out rest
    ⟨addHyp c R⟩ ⟨addHyp ih R⟩ ⟨addHyp run R⟩ ⟨Derivation.conjunctionRight hr⟩ ⟨addHyp m R⟩
  exact ⟨disjunctionElimination alternatives
    (Derivation.implicationIntroduction left) (Derivation.implicationIntroduction right)⟩

/-- One actual cons with an arbitrary filtered output: the checked open
filter law exposes the genuine filtered tail under its own existential. -/
private theorem consInclusion (E : Program 4) (code h tail seen ctx ty k out : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (inherited : Nonempty (Derivation body Γ (included E tail seen ctx ty k)))
    (run : Nonempty (Derivation body Γ (passGraph E out code seen ctx ty)))
    (member : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (memberGraph code k)) := by
  let up : α → α ⊕ Fin 1 := Sum.inl
  let rest : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let P : Formula (α ⊕ Fin 1) := reportBinder E out h tail seen ctx ty
  let Δ : List (Formula (α ⊕ Fin 1)) := P :: Γ.map weaken
  have keep : ∀ p ∈ Γ, p.relabel up ∈ Δ :=
    fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have input' := renameInto input up Δ keep
  rw [consGraphRename] at input'
  have inherited' := renameInto inherited up Δ keep
  rw [includedRename] at inherited'
  have member' := renameInto member up Δ keep
  rw [graphRename] at member'
  have row : Nonempty (Derivation body Δ (restRow E (out.relabel up) (h.relabel up)
      (tail.relabel up) rest (seen.relabel up) (ctx.relabel up) (ty.relabel up))) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have shape : weaken (memberGraph code k) =
      memberGraph (code.relabel up) (k.relabel up) := graphRename code k up
  have closed : Nonempty (Derivation body Δ (weaken (memberGraph code k))) := by
    rw [shape]
    exact withRow E (code.relabel up) (h.relabel up) (tail.relabel up) (seen.relabel up)
      (ctx.relabel up) (ty.relabel up) (k.relabel up) (out.relabel up) rest
      input' inherited' member' row
  obtain ⟨c⟩ := input
  obtain ⟨r⟩ := run
  obtain ⟨law⟩ := exact_OpenDirectedFilterCons E body α Γ code h tail seen ctx ty out
  have raw : Derivation body Γ (restReport E out h tail seen ctx ty) :=
    Derivation.implicationElimination law (Derivation.conjunctionIntroduction c r)
  have report : Derivation body Γ (existsOne P) := raw
  obtain ⟨closed⟩ := closed
  exact ⟨Derivation.existentialElimination report closed⟩

/-- At nil the actual pass output is the actual constant zero, so the
membership premise transports to the same nil; no bit is inserted. -/
private theorem nilInclusion (E : Program 4) (seen ctx ty k out : OTerm α)
    (run : Nonempty (Derivation body Γ (passGraph E out z seen ctx ty)))
    (member : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (memberGraph z k)) := by
  have value := nilRecover (constantZero 3) (filterStep E) out
    (![seen,ctx,ty] : Fin 3 → OTerm α) run
  obtain ⟨same⟩ := valueUnique (constantZero 3) out z (![seen,ctx,ty] : Fin 3 → OTerm α)
    value (zeroConstantValue (![seen,ctx,ty] : Fin 3 → OTerm α))
  exact headTransport scratchMember (suc z) out z (![k] : Fin 1 → OTerm α) ⟨same⟩ member

private theorem nilFromHit (E : Program 4) (seen ctx ty k : OTerm α)
    (hit : Nonempty (Derivation body Γ (hitGraph E z seen ctx ty k))) :
    Nonempty (Derivation body Γ (memberGraph z k)) := by
  apply hitCases E z seen ctx ty k (memberGraph z k) hit
  intro β j Δ out _ run member
  rw [graphRename,zRelabel]
  rw [zRelabel] at run
  exact nilInclusion E (seen.relabel j) (ctx.relabel j) (ty.relabel j) (k.relabel j) out
    run member

private theorem consFromHit (E : Program 4) (code h tail seen ctx ty k : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (inherited : Nonempty (Derivation body Γ (included E tail seen ctx ty k)))
    (hit : Nonempty (Derivation body Γ (hitGraph E code seen ctx ty k))) :
    Nonempty (Derivation body Γ (memberGraph code k)) := by
  apply hitCases E code seen ctx ty k (memberGraph code k) hit
  intro β j Δ out keep run member
  rw [graphRename]
  have input' := renameInto input j Δ keep
  rw [consGraphRename] at input'
  have inherited' := renameInto inherited j Δ keep
  rw [includedRename] at inherited'
  exact consInclusion E (code.relabel j) (h.relabel j) (tail.relabel j) (seen.relabel j)
    (ctx.relabel j) (ty.relabel j) (k.relabel j) out input' inherited' run member

/-- Base of the original list induction, at the literal nil code. -/
theorem atNil (E : Program 4) (seen ctx ty k : OTerm α) :
    Nonempty (Derivation body Γ (included E z seen ctx ty k)) := by
  let H := hitGraph E z seen ctx ty k
  obtain ⟨d⟩ := nilFromHit (body := body) (Γ := H :: Γ) E seen ctx ty k
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

/-- Constructor step of the original list induction, at an actual cons
graph, from the invariant at its real tail. -/
theorem atCons (E : Program 4) (code h tail seen ctx ty k : OTerm α)
    (input : Nonempty (Derivation body Γ (consGraph code h tail)))
    (inherited : Nonempty (Derivation body Γ (included E tail seen ctx ty k))) :
    Nonempty (Derivation body Γ (included E code seen ctx ty k)) := by
  let H := hitGraph E code seen ctx ty k
  obtain ⟨c⟩ := input
  obtain ⟨ih⟩ := inherited
  obtain ⟨d⟩ := consFromHit (body := body) (Γ := H :: Γ) E code h tail seen ctx ty k
    ⟨addHyp c H⟩ ⟨addHyp ih H⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionStepProof
