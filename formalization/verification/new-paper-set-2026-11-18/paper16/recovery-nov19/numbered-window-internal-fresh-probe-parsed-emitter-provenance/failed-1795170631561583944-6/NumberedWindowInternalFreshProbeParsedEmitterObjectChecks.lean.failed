module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterOpenAddressProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterShapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterGuardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterPayloadProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterObjectChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (programRename equalEqn)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalFreshProbeEmitter (packedEmitter emitSelected)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalFreshProbeEmitterPayloadProof (actualPayload)
open NumberedWindowInternalFreshProbeEmitterGraphProof (packedEmitterEquation)
open NumberedWindowInternalFreshProbeSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (takeUnary)
open NumberedWindowInternalFreshProbeParsedEmitter
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets
open NumberedWindowInternalFreshProbeParsedEmitterOpenAddressProof (exactOpenCoordinates)
open NumberedWindowInternalFreshProbeParsedEmitterGuardProof (checkedGuard guardReports gatePreserves)
open NumberedWindowInternalFreshProbeParsedEmitterReportProof (rawPrograms reportCases)
open NumberedWindowInternalFreshProbeParsedEmitterShapeSyntaxProof (parsedIntro parsedRename)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem emittedOnReports (scalarProg bound : Program 1) (q u c d n : OTerm α)
    (guard : Nonempty (Derivation body Γ (programGraph (selectedGuard scalarProg) (suc z) ![q])))
    (payload : Nonempty (Derivation body Γ (programGraph (emitSelected (selected scalarProg bound)) u ![q])))
    (hc : Nonempty (Derivation body Γ (programGraph rawContext c ![q])))
    (hd : Nonempty (Derivation body Γ (programGraph rawDomain d ![q])))
    (hn : Nonempty (Derivation body Γ (programGraph (applyUnary bound rawLeast) n ![q]))) :
    Nonempty (Derivation body Γ (equal u (packedFreeTerm c d n))) := by
  let p := selected scalarProg bound
  let children := Fin.cons p.context (Fin.cons p.domain (Fin.cons p.name Fin.elim0))
  have c0 := gatePreserves scalarProg rawContext q c guard hc
  have c1 := gatePreserves scalarProg rawDomain q d guard hd
  have c2 := gatePreserves scalarProg (applyUnary bound rawLeast) q n guard hn
  have he := compositionRecover packedEmitter children u ![q] ![c,d,n] payload
    (fun i => Fin.cases c0 (Fin.cases c1 (Fin.cases c2 (fun k => Fin.elim0 k))) i)
  rw [equalEqn]
  exact packedEmitterEquation u c d n he

private theorem assemble (scalarProg bound : Program 1) (q u : OTerm α) (ys : Fin 6 → OTerm α)
    (guard : Nonempty (Derivation body Γ (programGraph (selectedGuard scalarProg) (suc z) ![q])))
    (payload : Nonempty (Derivation body Γ (programGraph (emitSelected (selected scalarProg bound)) u ![q])))
    (values : ∀ i, Nonempty (Derivation body Γ (programGraph (rawPrograms bound i) (ys i) ![q]))) :
    Nonempty (Derivation body Γ (parsedFreshAt bound q u)) := by
  have hc : Nonempty (Derivation body Γ (programGraph rawContext (ys 0) ![q])) := values 0
  have hr : Nonempty (Derivation body Γ (programGraph rawResult (ys 1) ![q])) := values 1
  have hd : Nonempty (Derivation body Γ (programGraph rawDomain (ys 2) ![q])) := values 2
  have he : Nonempty (Derivation body Γ (programGraph rawCodomain (ys 3) ![q])) := values 3
  have hk : Nonempty (Derivation body Γ (programGraph rawLeast (ys 4) ![q])) := values 4
  have hn : Nonempty (Derivation body Γ (programGraph (applyUnary bound rawLeast) (ys 5) ![q])) := values 5
  obtain ⟨node,arrow⟩ := guardReports scalarProg q guard
  obtain ⟨dc⟩ := hc
  obtain ⟨dr⟩ := hr
  obtain ⟨dd⟩ := hd
  obtain ⟨de⟩ := he
  obtain ⟨dk⟩ := hk
  have hAddress : Nonempty (Derivation body Γ (addressReports q (ys 0) (ys 1) (ys 4))) :=
    ⟨Derivation.conjunctionIntroduction dc (Derivation.conjunctionIntroduction dr dk)⟩
  have hArrow : Nonempty (Derivation body Γ (arrowReports q (ys 2) (ys 3))) :=
    ⟨Derivation.conjunctionIntroduction dd de⟩
  have hShape := exactOpenCoordinates body α Γ q (ys 0) (ys 1) (ys 2) (ys 3) (ys 4)
    node arrow hAddress hArrow
  have hBound := takeUnary bound rawLeast (ys 5) q (ys 4) hn ⟨dk⟩
  have hEmit := emittedOnReports scalarProg bound q u (ys 0) (ys 2) (ys 5) guard payload ⟨dc⟩ ⟨dd⟩ hn
  exact parsedIntro bound q u ys hAddress hArrow hShape hBound hEmit

theorem exact_OpenAddressArrowCoordinates : ExactOpenAddressArrowCoordinates := exactOpenCoordinates

theorem exact_OpenParsedFresh : ExactOpenParsedFresh := by
  intro scalarProg bound body α Γ q u h
  have hguard := checkedGuard scalarProg bound q u h
  have hpayload := actualPayload (selected scalarProg bound) q u h
  apply reportCases bound q (parsedFreshAt bound q u)
  intro β j Δ ys hJ values
  rw [parsedRename]
  have guard := renameInto hguard j Δ hJ
  have payload := renameInto hpayload j Δ hJ
  simp only [programRename,unaryRename,sucRelabel,zRelabel] at guard
  simp only [programRename,unaryRename] at payload
  exact assemble scalarProg bound (q.relabel j) (u.relabel j) ys guard payload values

#print axioms exact_OpenAddressArrowCoordinates
#print axioms exact_OpenParsedFresh
end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterObjectChecks
