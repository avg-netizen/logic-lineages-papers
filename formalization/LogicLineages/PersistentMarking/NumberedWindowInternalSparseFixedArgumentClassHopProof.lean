module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFixedArgumentRawHopProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFixedArgumentClassHopProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalCoverCombinedRestrictedFormationTargets (thinFormation)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow thinSyntaxWindow)
open NumberedWindowInternalSparseCoveredWindowOpenReportProof (exact_CoveredWindowReport)
open NumberedWindowInternalSparseFixedArgumentRawHopProof (windowIdentity formed)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (casesLeast hasRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparseAddressSingletonTargets (singletonCertificate)
open NumberedWindowInternalSparseAddressSingletonCoreProof (fromCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph5Rename)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem numeralRename {β : Type} (n : Nat) (j : α → β) :
    (numeral n : OTerm α).relabel j = numeral n := by
  induction n with
  | zero => exact zRelabel j
  | succ n ih =>
    simpa only [numeral,sucRelabel] using congrArg ID1Completion.InternalTagArithmeticSyntaxProof.suc ih

private theorem witnessRename {β : Type} (w : OTerm α) (j : α → β) :
    (functionWitnessTerm w).relabel j = functionWitnessTerm (w.relabel j) := by
  unfold functionWitnessTerm
  rw [rawConsRename,rawConsRename,zRelabel,numeralRename]

private theorem leastOfWindow (C : Program 3) (X : Program 2) (s : Settings)
    (baseW : Program 3) (V : Program 1) (ctx ty q : OTerm α)
    (h : Nonempty (Derivation body Γ (windowAt (thinMatchingWindow C s baseW V) ctx ty q))) :
    Nonempty (Derivation body Γ (hasLeast C X (thinMatchingWindow C s baseW V) s ctx ty q)) := by
  rw [windowIdentity] at h ⊢
  obtain ⟨rule⟩ := exact_CoveredWindowReport C X s (thinSyntaxWindow baseW V) body α Γ ctx ty q
  obtain ⟨known⟩ := h
  have report := Derivation.implicationElimination rule known
  exact ⟨Derivation.conjunctionRight (Derivation.conjunctionRight report)⟩

/-- Fix the raw argument. For the actual given typed raw hop, derive both
canonical class calls on the *raw* applications and the actual accepted
singleton in that same physical fiber. No representative function is inserted. -/
theorem classHopCases (C root other baseW : Program 3) (X : Program 2) (s : Settings) (V : Program 1)
    (ctx dom cod arg q w r : OTerm α) (goal : Formula α) :
    let W := thinMatchingWindow C s baseW V
    let raw := typedRaw5 root other W V
    let least := packedLeastProgram C X W s
    Nonempty (Derivation body Γ (thinFormation W ctx dom cod arg)) →
    Nonempty (Derivation body Γ (programGraph raw (suc z) ![ctx,rawCons dom cod,q,w,r])) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (a b : OTerm β),
      let l := auxiliaryTerm (dom.relabel j) (cod.relabel j) (q.relabel j) (arg.relabel j)
      let y := auxiliaryTerm (dom.relabel j) (cod.relabel j) (r.relabel j) (arg.relabel j)
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (leastGraph C X W s (ctx.relabel j) (cod.relabel j) l a)) →
      Nonempty (Derivation body Δ (leastGraph C X W s (ctx.relabel j) (cod.relabel j) y b)) →
      Nonempty (Derivation body Δ (positiveAt raw least (ctx.relabel j) (cod.relabel j) a
        (singletonCertificate b l (functionWitnessTerm (w.relabel j)) y) b)) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal) := by
  intro W raw least ready source next
  let qApp := auxiliaryTerm dom cod q arg
  let rApp := auxiliaryTerm dom cod r arg
  obtain ⟨step⟩ := formed C root other baseW X s V ctx dom cod arg q w r ready source
  have qLeast := leastOfWindow C X s baseW V ctx cod qApp ⟨Derivation.conjunctionLeft step⟩
  have rLeast := leastOfWindow C X s baseW V ctx cod rApp
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight step)⟩
  have rap : Nonempty (Derivation body Γ
      (programGraph raw (suc z) ![ctx,cod,qApp,functionWitnessTerm w,rApp])) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight step)⟩
  apply casesLeast C X W s ctx cod qApp goal qLeast
  intro β j Δ a keep lcall
  have later := renameInto rLeast j Δ keep
  rw [hasRename] at later
  apply casesLeast C X W s (ctx.relabel j) (cod.relabel j) (rApp.relabel j) _ later
  intro γ k Θ b preserve rcall
  have left := renameInto lcall k Θ preserve
  rw [leastRename] at left
  have finalRaw := renameInto (renameInto rap j Δ keep) k Θ preserve
  rw [graph5Rename,graph5Rename] at finalRaw
  have compose : ∀ p ∈ Γ, p.relabel (k ∘ j) ∈ Θ := by
    intro p hp
    simpa only [formulaRelabelComposition] using preserve (p.relabel j) (keep p hp)
  let J := k ∘ j
  let cx := ctx.relabel J
  let cd := cod.relabel J
  let l := auxiliaryTerm (dom.relabel J) cd (q.relabel J) (arg.relabel J)
  let y := auxiliaryTerm (dom.relabel J) cd (r.relabel J) (arg.relabel J)
  let witness := functionWitnessTerm (w.relabel J)
  have hL : Nonempty (Derivation body Θ (leastGraph C X W s cx cd l (a.relabel k))) := by
    simpa only [qApp,J,cx,cd,l,Term.relabel_relabel,auxiliaryRename] using left
  have hR : Nonempty (Derivation body Θ (leastGraph C X W s cx cd y b)) := by
    simpa only [rApp,J,cx,cd,y,Term.relabel_relabel,auxiliaryRename] using rcall
  have hRaw : Nonempty (Derivation body Θ (programGraph raw (suc z) ![cx,cd,l,witness,y])) := by
    simpa only [qApp,rApp,J,cx,cd,l,y,witness,Term.relabel_relabel,auxiliaryRename,
      witnessRename,sucRelabel,zRelabel] using finalRaw
  obtain ⟨p⟩ := hRaw
  obtain ⟨lG⟩ := hL
  obtain ⟨rG⟩ := hR
  have full := fromCalls raw least cx cd (a.relabel k) b l witness y
    ⟨Derivation.conjunctionIntroduction p (Derivation.conjunctionIntroduction lG rG)⟩
  simpa only [formulaRelabelComposition,J] using next γ J Θ (a.relabel k) b compose ⟨lG⟩ ⟨rG⟩ full

#print axioms classHopCases
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFixedArgumentClassHopProof
