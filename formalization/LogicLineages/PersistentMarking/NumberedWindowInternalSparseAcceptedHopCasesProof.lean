module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenGateProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenCallsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchQueryCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAcceptedHopCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationCertificateConstructorsSupportProof (unaryRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalControlGraphSupportProof (projectionValue programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelope (hopGood hopTarget hopSource hopWitness hopRawTarget)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary hopCertified)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename)
open NumberedWindowInternalSparsePathAdvance
open NumberedWindowInternalSparsePathAdvanceTargets
open NumberedWindowInternalSparsePathAdvanceOpenGateProof (recoverGate continued)
open NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof (coords quadRename)
open NumberedWindowInternalSparsePathAdvanceOpenCallsProof (callsRead)
open NumberedWindowInternalScratchQueryCasesProof (queryCases)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem onHop (k : Program 1) (out ctx ty current hop : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (atHop k) out (coords ctx ty current hop)))) :
    Nonempty (Derivation body Γ (unary k out hop)) :=
  unaryRecover k (.projection 3) out hop (coords ctx ty current hop) h
    (projectionValue 3 (coords ctx ty current hop))

private theorem inspect (raw : Program 5) (least : Program 3) (ctx ty current hop target : OTerm α)
    (live : Nonempty (Derivation body Γ (selectedGraph raw least (suc target) ctx ty (suc current) hop))) :
    Nonempty (Derivation body Γ (acceptedGuard raw least ctx ty (suc current) hop)) ∧
    Nonempty (Derivation body Γ (unary hopGood (suc z) hop)) ∧
    Nonempty (Derivation body Γ (unary hopTarget target hop)) := by
  let s := suc current
  let xs := coords ctx ty s hop
  obtain ⟨cert⟩ := recoverGate raw least ctx ty s hop target live
  have accepted : Nonempty (Derivation body Γ (acceptedGuard raw least ctx ty s hop)) :=
    ⟨Derivation.conjunctionLeft cert⟩
  obtain ⟨tests⟩ := conjunctionRecover statePresent (continued raw least) xs accepted
  obtain ⟨tail⟩ := conjunctionRecover (atHop hopGood)
    (conjunction (rawCall raw) (conjunction (fromMatches least) (toMatches least))) xs
    ⟨Derivation.conjunctionRight tests⟩
  exact ⟨accepted,onHop hopGood (suc z) ctx ty s hop ⟨Derivation.conjunctionLeft tail⟩,
    onHop hopTarget target ctx ty s hop ⟨Derivation.conjunctionRight cert⟩⟩

private def queries : Fin 3 → Program 1 := ![hopSource,hopWitness,hopRawTarget]

/-- Open the original raw components of the *actual successful* head
advance. The visible least reports, class transition, and chosen selector
coordinates are kept; no guessed envelope or independent typed raw edge. -/
theorem advanceCases (raw : Program 5) (least : Program 3)
    (ctx ty current hop target : OTerm α) (goal : Formula α)
    (live : Nonempty (Derivation body Γ (selectedGraph raw least (suc target) ctx ty (suc current) hop)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (q w r : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (hopCertified (hop.relabel j) (target.relabel j) q w r)) →
      Nonempty (Derivation body Δ (actualCalls raw least (ctx.relabel j) (ty.relabel j)
        (current.relabel j) (target.relabel j) q w r)) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  obtain ⟨ok,good,targetCode⟩ := inspect raw least ctx ty current hop target live
  apply queryCases queries ![hop] goal
  intro β j ys Δ keep fields
  rw [inputsRename] at fields
  have legit := renameInto good j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at legit
  have sameTarget := renameInto targetCode j Δ keep
  rw [unaryRename] at sameTarget
  have hOK := renameInto ok j Δ keep
  simp only [acceptedGuard,quadRename,sucRelabel,zRelabel] at hOK
  obtain ⟨a⟩ := legit
  obtain ⟨b⟩ := sameTarget
  obtain ⟨q⟩ := fields 0
  obtain ⟨w⟩ := fields 1
  obtain ⟨r⟩ := fields 2
  have owner : Nonempty (Derivation body Δ (hopCertified (hop.relabel j) (target.relabel j)
      (ys 0) (ys 1) (ys 2))) :=
    ⟨Derivation.conjunctionIntroduction a (Derivation.conjunctionIntroduction b
      (Derivation.conjunctionIntroduction q (Derivation.conjunctionIntroduction w r)))⟩
  have calls := callsRead raw least (ctx.relabel j) (ty.relabel j) (current.relabel j)
    (hop.relabel j) (target.relabel j) (ys 0) (ys 1) (ys 2) owner hOK
  exact next β j Δ (ys 0) (ys 1) (ys 2) keep owner calls

#print axioms advanceCases
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAcceptedHopCasesProof
