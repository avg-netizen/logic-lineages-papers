module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentGapCoreProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityGapProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentGapProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalQuotientComparisonProof (equalToNext)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseFieldInductionTargets (malformed nonzero)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph)
open NumberedWindowInternalSparsePositiveIterationBindingProof (scratchRename)
open NumberedWindowInternalSparsePositiveTerminalityFuelProof (fuelSuccessorCases)
open NumberedWindowInternalSparsePositiveTerminalitySeedProof (scratchCases)
open NumberedWindowInternalSparsePositiveTerminalityGapProof (gapRename)
open NumberedWindowInternalSparsePositiveChosenConsSyntaxProof (finishGraph finishRename)
open NumberedWindowInternalSparsePositiveDeadCurrentTargets
open NumberedWindowInternalSparsePositiveDeadCurrentGapCoreProof (deadAtSeeds)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem chooseDead (raw : Program 5) (least : Program 3) (ctx ty current cert pred old : OTerm α)
    (eq : Nonempty (Derivation body Γ (eqn cert (suc pred))))
    (bad : Nonempty (Derivation body Γ (malformed cert)))
    (before : Nonempty (Derivation body Γ (scratchGraph old cert current))) :
    Nonempty (Derivation body Γ (finishGraph raw least z ctx ty current cert)) := by
  apply scratchCases z z (finishGraph raw least z ctx ty current cert)
  intro β j Δ dead hJ after
  rw [finishRename,zRelabel]
  simp only [zRelabel] at after
  have e := renameInto eq j Δ hJ
  rw [eqnRelabel,sucRelabel] at e
  have b := renameInto bad j Δ hJ
  rw [gapRename] at b
  have p := renameInto before j Δ hJ
  rw [scratchRename] at p
  exact deadAtSeeds raw least (ctx.relabel j) (ty.relabel j) (current.relabel j)
    (cert.relabel j) (pred.relabel j) (old.relabel j) dead e b p after

private theorem choosePrior (raw : Program 5) (least : Program 3) (ctx ty current cert pred : OTerm α)
    (eq : Nonempty (Derivation body Γ (eqn cert (suc pred))))
    (bad : Nonempty (Derivation body Γ (malformed cert))) :
    Nonempty (Derivation body Γ (finishGraph raw least z ctx ty current cert)) := by
  apply scratchCases cert current (finishGraph raw least z ctx ty current cert)
  intro β j Δ old hJ before
  rw [finishRename,zRelabel]
  have e := renameInto eq j Δ hJ
  rw [eqnRelabel,sucRelabel] at e
  have b := renameInto bad j Δ hJ
  rw [gapRename] at b
  exact chooseDead raw least (ctx.relabel j) (ty.relabel j) (current.relabel j)
    (cert.relabel j) (pred.relabel j) old e b before

theorem gapValue (raw : Program 5) (least : Program 3) (ctx ty current cert : OTerm α)
    (bad : Nonempty (Derivation body Γ (malformed cert))) :
    Nonempty (Derivation body Γ (finishGraph raw least z ctx ty current cert)) := by
  obtain ⟨b⟩ := bad
  have nz : Nonempty (Derivation body Γ (eqn cert z).not) := by
    rw [← equalEqn]
    exact ⟨Derivation.conjunctionLeft b⟩
  have fuel : Nonempty (Derivation body Γ (ltF cert (suc cert))) := ⟨equalToNext (refl cert)⟩
  apply fuelSuccessorCases cert cert (finishGraph raw least z ctx ty current cert) fuel nz
  intro β j Δ pred hJ eq _
  rw [finishRename,zRelabel]
  have bad' := renameInto ⟨b⟩ j Δ hJ
  rw [gapRename] at bad'
  exact choosePrior raw least (ctx.relabel j) (ty.relabel j) (current.relabel j) (cert.relabel j) pred eq bad'

theorem gapZero : OpenMalformedFinishZero := by
  intro body raw least α ctx ty current cert
  let h := malformed cert
  obtain ⟨d⟩ := gapValue (body := body) (Γ := [h]) raw least ctx ty current cert
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentGapProof
