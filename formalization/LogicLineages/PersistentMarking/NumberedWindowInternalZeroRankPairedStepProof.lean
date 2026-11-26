module

public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankStepLiveProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPairedStepProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof (call6)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalZeroRankAdvance (zeroOutput)
open NumberedWindowInternalParameterizedPositiveFold
open NumberedWindowInternalZeroRankStepTransportProof (Report zeroTail zeroTailRename)
open NumberedWindowInternalZeroRankStepDeadProof (exact_OpenFilteredStepKeepsZero)
open NumberedWindowInternalZeroRankStepLiveProof (exact_OpenFilteredStepWhenLive notRename)

attribute [local irreducible] programGraph

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def liveAgrees {α : Type} (f u : OTerm α) : Formula α :=
  (zeroTail f).not.imp (eqn f u)

theorem liveAgreesRename {α β : Type} (f u : OTerm α) (j : α → β) :
    (liveAgrees f u).relabel j = liveAgrees (f.relabel j) (u.relabel j) := by
  have impRename (p q : Formula α) : (p.imp q).relabel j = (p.relabel j).imp (q.relabel j) := rfl
  simp only [liveAgrees,impRename,notRename,zeroTailRename,eqnRelabel]

private theorem moveState (P : Program 6) (out k f u c ty start cert : OTerm α)
    (equal : Nonempty (Derivation B Γ (eqn f u)))
    (held : Report (B := B) (Γ := Γ) P out (call6 k f c ty start cert)) :
    Report (B := B) (Γ := Γ) P out (call6 k u c ty start cert) := by
  unfold Report programGraph at held ⊢
  apply graphInputTransport B α 6 Γ (OrdinaryArithmetic.graphFormula P) out
    (call6 k f c ty start cert) (call6 k u c ty start cert) _ held
  intro i
  rw [ID1Completion.InternalSourceInversionSupportProof.onEquality]
  change Nonempty (Derivation B Γ (eqn (call6 k f c ty start cert i) (call6 k u c ty start cert i)))
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c =>
    Fin.cases ?_ (fun d => Fin.cases ?_ (fun e => Fin.cases ?_ (fun q => Fin.elim0 q) e) d) c) b) a) i
  · exact ⟨ID1Completion.InternalTagArithmeticSupportProof.refl k⟩
  · exact equal
  · exact ⟨ID1Completion.InternalTagArithmeticSupportProof.refl c⟩
  · exact ⟨ID1Completion.InternalTagArithmeticSupportProof.refl ty⟩
  · exact ⟨ID1Completion.InternalTagArithmeticSupportProof.refl start⟩
  · exact ⟨ID1Completion.InternalTagArithmeticSupportProof.refl cert⟩

/-- Pair the actual step graphs at exactly the same fuel and parameters.
A live filtered output implies the two scratch outputs agree. -/
theorem exact_OpenZeroRankPairedStep (g : Program 1) (raw : Program 5) (least : Program 3)
    (k f u fn un c ty start cert : OTerm α)
    (older : Nonempty (Derivation B Γ (liveAgrees f u)))
    (filterStep : Report (B := B) (Γ := Γ) (stepAt (zeroOutput g (advance raw least)))
      fn (call6 k f c ty start cert))
    (plainStep : Report (B := B) (Γ := Γ) (stepAt (advance raw least))
      un (call6 k u c ty start cert)) :
    Nonempty (Derivation B Γ (liveAgrees fn un)) := by
  let keep := (zeroTail fn).not
  let Δ := keep :: Γ
  have liveNow : Derivation B Δ keep := Derivation.hypothesis List.mem_cons_self
  have fHeld := withHyp filterStep keep
  have uHeld := withHyp plainStep keep
  have prev := withHyp older keep
  have pay : Nonempty (Derivation B Δ (eqn fn un)) := by
    apply formulaCases (zeroTail f) (eqn fn un)
    · have stopped := exact_OpenFilteredStepKeepsZero (B := B) (Γ := zeroTail f :: Δ)
        g raw least (call6 k f c ty start cert) fn
        ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp fHeld (zeroTail f))
      obtain ⟨stopped⟩ := stopped
      obtain ⟨neg⟩ := withHyp (Nonempty.intro liveNow) (zeroTail f)
      exact ⟨Derivation.explosion (Derivation.implicationElimination neg stopped)⟩
    · obtain ⟨h⟩ := withHyp prev (zeroTail f).not
      have pre : Derivation B ((zeroTail f).not :: Δ) (zeroTail f).not :=
        Derivation.hypothesis List.mem_cons_self
      have eq := Derivation.implicationElimination h pre
      have atFn := exact_OpenFilteredStepWhenLive (B := B) (Γ := (zeroTail f).not :: Δ)
        g raw least (call6 k f c ty start cert) fn
        (withHyp (Nonempty.intro liveNow) (zeroTail f).not) (withHyp fHeld (zeroTail f).not)
      have new := moveState (stepAt (advance raw least)) fn k f u c ty start cert ⟨eq⟩ atFn
      exact valueUnique (stepAt (advance raw least)) fn un (call6 k u c ty start cert)
        new (withHyp uHeld (zeroTail f).not)
  obtain ⟨d⟩ := pay
  exact ⟨Derivation.implicationIntroduction d⟩

#print axioms exact_OpenZeroRankPairedStep
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPairedStepProof
