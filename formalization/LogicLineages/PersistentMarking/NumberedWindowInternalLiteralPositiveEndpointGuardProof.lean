module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPositiveCertificateRowsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPositiveEndpointGuardProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover conjunctionAccept)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalLiteralPositiveCertificateRowsProof (D)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeOne)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def endpointAt (i : Program 1) (slot : Fin 3) : Program 3 :=
  .composition i (Fin.cons (.projection slot) Fin.elim0)

/-- Keep the original three-slot addressed positive program, and expose
both actual scalar guards at the same two original tape positions. -/
def positiveEndpointGuard (i : Program 1) (P : Program 3) : Program 3 :=
  conjunction P (conjunction (endpointAt i 0) (endpointAt i 2))

def PositiveEndpointFit (i : Program 1) (P : Program 3) : Prop :=
  ∀ x cert y : Nat, evaluate P (x ::ᵥ cert ::ᵥ y ::ᵥ nil) = 1 →
    evaluate i (x ::ᵥ nil) = 1 ∧ evaluate i (y ::ᵥ nil) = 1

theorem exact_PositiveEndpointGuardCalibration (i : Program 1) (P : Program 3)
    (fit : PositiveEndpointFit i P)
    (boolean : ∀ xs, evaluate P xs = 0 ∨ evaluate P xs = 1) (x cert y : Nat) :
    evaluate (positiveEndpointGuard i P) (x ::ᵥ cert ::ᵥ y ::ᵥ nil) = evaluate P (x ::ᵥ cert ::ᵥ y ::ᵥ nil) := by
  rw [positiveEndpointGuard,actualConjunctionEvaluation,actualConjunctionEvaluation,
    endpointAt,endpointAt,compositeOne,compositeOne]
  change (if evaluate P (x ::ᵥ cert ::ᵥ y ::ᵥ nil) = 1 ∧
    (if evaluate i (x ::ᵥ nil) = 1 ∧ evaluate i (y ::ᵥ nil) = 1 then 1 else 0) = 1 then 1 else 0) = _
  rcases boolean (x ::ᵥ cert ::ᵥ y ::ᵥ nil) with no | yes
  · simp [no]
  · obtain ⟨left,right⟩ := fit x cert y yes
    simp [yes,left,right]

private theorem introAt (i : Program 1) (slot : Fin 3) (xs : Fin 3 → OTerm α)
    (yes : D B Γ (unary i (suc z) (xs slot))) :
    D B Γ (programGraph (endpointAt i slot) (suc z) xs) := by
  apply compositionValue i (Fin.cons (.projection slot) Fin.elim0) (suc z) xs ![xs slot] yes
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue slot xs

private theorem elimAt (i : Program 1) (slot : Fin 3) (xs : Fin 3 → OTerm α)
    (yes : D B Γ (programGraph (endpointAt i slot) (suc z) xs)) :
    D B Γ (unary i (suc z) (xs slot)) := by
  apply compositionRecover i (Fin.cons (.projection slot) Fin.elim0) (suc z) xs ![xs slot] yes
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue slot xs

theorem exact_OpenPositiveEndpointGuardIntro (i : Program 1) (P : Program 3) (x cert y : OTerm α)
    (arc : D B Γ (programGraph P (suc z) ![x,cert,y]))
    (left : D B Γ (unary i (suc z) x)) (right : D B Γ (unary i (suc z) y)) :
    D B Γ (programGraph (positiveEndpointGuard i P) (suc z) ![x,cert,y]) :=
  conjunctionAccept P (conjunction (endpointAt i 0) (endpointAt i 2)) ![x,cert,y] arc
    (conjunctionAccept (endpointAt i 0) (endpointAt i 2) ![x,cert,y]
      (introAt i 0 ![x,cert,y] left) (introAt i 2 ![x,cert,y] right))

theorem exact_OpenPositiveEndpointGuardElim (i : Program 1) (P : Program 3) (x cert y : OTerm α)
    (arc : D B Γ (programGraph (positiveEndpointGuard i P) (suc z) ![x,cert,y])) :
    D B Γ (programGraph P (suc z) ![x,cert,y]) ∧
    D B Γ (unary i (suc z) x) ∧ D B Γ (unary i (suc z) y) := by
  obtain ⟨rows⟩ := conjunctionRecover P (conjunction (endpointAt i 0) (endpointAt i 2)) ![x,cert,y] arc
  obtain ⟨sides⟩ := conjunctionRecover (endpointAt i 0) (endpointAt i 2) ![x,cert,y]
    ⟨Derivation.conjunctionRight rows⟩
  exact ⟨⟨Derivation.conjunctionLeft rows⟩,elimAt i 0 ![x,cert,y] ⟨Derivation.conjunctionLeft sides⟩,
    elimAt i 2 ![x,cert,y] ⟨Derivation.conjunctionRight sides⟩⟩

#print axioms exact_PositiveEndpointGuardCalibration
#print axioms exact_OpenPositiveEndpointGuardIntro
#print axioms exact_OpenPositiveEndpointGuardElim
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPositiveEndpointGuardProof
