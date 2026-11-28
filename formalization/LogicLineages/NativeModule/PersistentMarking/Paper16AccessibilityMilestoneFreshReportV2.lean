module

public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterObjectChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshReportV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (compositionValue successorValue equalEqn)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeEmitter (chooseFresh emitSelected packedEmitter)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalFreshProbeEmitterObjectChecks (exact_PackedFreeEmitterGraph)
open NumberedWindowInternalFreshProbeParsedEmitter
open NumberedWindowInternalFreshProbeParsedEmitterGuardProof (gatePreserves)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA)
open NumberedWindowInternalProbeTargets (OTerm freshAt)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)

attribute [local irreducible] programGraph

/-- Construct the actual positive fresh report from its scalar and parser
guards and its original context, domain, and bound programs. -/
theorem exact_ChosenFreshFromReports {body : Positive (Fin 1)}
    {α : Type} {Γ : List (Formula α)} (v : Inputs) (q ctx dom name : OTerm α)
    (scalar : Nonempty (Derivation body Γ (programGraph v.scalarProg (suc z) ![q])))
    (address : Nonempty (Derivation body Γ (programGraph addressGood (suc z) ![q])))
    (arrow : Nonempty (Derivation body Γ (programGraph arrowGood (suc z) ![q])))
    (contextReport : Nonempty (Derivation body Γ (programGraph rawContext ctx ![q])))
    (domainReport : Nonempty (Derivation body Γ (programGraph rawDomain dom ![q])))
    (boundReport : Nonempty (Derivation body Γ
      (programGraph (applyUnary v.freshBound rawLeast) name ![q]))) :
    Nonempty (Derivation body Γ (freshAt (chosenA v) q (packedFreeTerm ctx dom name))) := by
  let p := selected v.scalarProg v.freshBound
  let u := packedFreeTerm ctx dom name
  have parsed : Nonempty (Derivation body Γ (programGraph parserGuard (suc z) ![q])) := by
    rw [parserGuard, exact_DispatchControlAST.2.2.2.2.2]
    exact conjunctionAccept addressGood arrowGood ![q] address arrow
  have guard : Nonempty (Derivation body Γ (programGraph (selectedGuard v.scalarProg) (suc z) ![q])) := by
    unfold selectedGuard
    apply normalizeAccept
    rw [exact_DispatchControlAST.2.2.2.2.2]
    exact conjunctionAccept v.scalarProg parserGuard ![q] scalar parsed
  have ctx' := gatePreserves v.scalarProg rawContext q ctx guard contextReport
  have dom' := gatePreserves v.scalarProg rawDomain q dom guard domainReport
  have name' := gatePreserves v.scalarProg (applyUnary v.freshBound rawLeast) q name guard boundReport
  obtain ⟨emitter⟩ := exact_PackedFreeEmitterGraph body α Γ u ctx dom name
  have checked : Derivation body Γ (equal u u) := by
    rw [equalEqn]
    exact refl u
  have packed : Nonempty (Derivation body Γ (programGraph packedEmitter u ![ctx, dom, name])) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight emitter) checked⟩
  have payload : Nonempty (Derivation body Γ (programGraph (emitSelected p) u ![q])) := by
    unfold emitSelected
    apply compositionValue packedEmitter _ u ![q] ![ctx, dom, name] packed
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
    · exact ctx'
    · exact dom'
    · exact name'
  let positive : Program 1 := .composition .succ (Fin.cons (emitSelected p) Fin.elim0)
  have emitted : Nonempty (Derivation body Γ (programGraph positive (suc u) ![q])) := by
    apply compositionValue .succ _ (suc u) ![q] ![u] (successorValue ![u])
    intro i
    obtain rfl := Fin.eq_zero i
    exact payload
  change Nonempty (Derivation body Γ (programGraph (chooseFresh p) (suc u) ![q]))
  rw [chooseFresh, exact_DispatchControlAST.2.2.2.2.1, exact_DispatchControlAST.1]
  exact successorBranchIntro p.good (constantZero 1) positive (suc u) z ![q] guard emitted

#print axioms exact_ChosenFreshFromReports

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshReportV2
