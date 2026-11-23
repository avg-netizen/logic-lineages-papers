module

public import LogicLineages.NativeModule.PersistentMarking.ObservationLambda

@[expose] public section

namespace LogicLineages.PersistentMarking.ObservationLambdaTargets
open Spine NameBridge DecisionInventory DecisionPorts DecisionObservations ObservationLambda

def FirstSound : Prop := ∀ Γ i, firstUnused Γ = some i → Γ[i]? = some none
def FirstComplete : Prop := ∀ Γ, used Γ < Γ.length → ∃ i, firstUnused Γ = some i

def FillExact : Prop := ∀ (Γ : Context) (i : Nat) (σ : Ty), Γ[i]? = some none →
  (fillSlot Γ i σ).length = Γ.length ∧ Extends Γ (fillSlot Γ i σ) ∧
  (fillSlot Γ i σ)[i]? = some (some σ) ∧ used (fillSlot Γ i σ) = used Γ + 1

def FillWellFormed : Prop := ∀ K B Γ i σ,
  WellFormed K B Γ → Γ[i]? = some none → σ ∈ K → WellFormed K B (fillSlot Γ i σ)

def AssignmentWeakening : Prop := ∀ V Γ Δ stack vs,
  Extends Γ Δ → Assignment V Γ stack vs → Assignment V Δ stack vs

def AssignmentPrepend : Prop := ∀ V Γ stack vs i σ,
  Assignment V Γ stack vs → Γ[i]? = some none →
  Assignment V (fillSlot Γ i σ) (σ::stack) (.cons (.free σ (portName V i)) vs)

/- The old tuple removes external slots above the still-retained new binder.
This states the genuine depth-indexed bound-slot law, not application staging. -/
def OpeningCoherence : Prop := ∀ vs σ x d q, FreeValues vs →
  substitute (.cons (.free σ x) .nil) d (substitute vs (d+1) q) =
    substitute (.cons (.free σ x) vs) d q

def LambdaReflection : Prop := ∀ vs q σ body, FreeValues vs →
  openOccurrence vs q = .lam σ body →
  ∃ originalBody, q = .lam σ originalBody ∧ body = substitute vs 1 originalBody

/- Supporting canonical-port closure. The domain-membership interface must
be discharged internally when assembling the source recursive closure lemma. -/
def LambdaDescent : Prop := ∀ S K V B Γ t υ σ τ body,
  PaperTerm S t υ → Ordinary t → WellFormed K B Γ → σ ∈ K →
  Expr.lam σ body ∈ observations V B Γ t (.arrow σ τ) →
  ∃ i, firstUnused Γ = some i ∧
    let Δ := fillSlot Γ i σ
    WellFormed K B Δ ∧ Extends Γ Δ ∧ used Δ = used Γ + 1 ∧
    openBody σ (portName V i) body ∈ observations V B Δ t τ
end LogicLineages.PersistentMarking.ObservationLambdaTargets
