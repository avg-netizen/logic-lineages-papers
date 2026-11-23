module

public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenCompareProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue outputTransport)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCompositionCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowExchangeAlgorithm (bits)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalMeasuredExchangeThinDefinitions (atSlot compareMeasurements)
open NumberedWindowInternalMeasuredExchangeThinOpenTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem slotForward (M : Program 1) (i : Fin 2) (out : OTerm α) (xs : Fin 2 → OTerm α)
    (h : Nonempty (Derivation body Γ (unary M out (xs i)))) :
    Nonempty (Derivation body Γ (programGraph (atSlot M i) out xs)) := by
  apply compositionValue M (fun _ : Fin 1 => .projection i) out xs ![xs i] h
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue i xs

private theorem slotBackward (M : Program 1) (i : Fin 2) (out : OTerm α) (xs : Fin 2 → OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (atSlot M i) out xs))) :
    Nonempty (Derivation body Γ (unary M out (xs i))) := by
  apply compositionRecover M (fun _ : Fin 1 => .projection i) out xs ![xs i] h
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue i xs

theorem compareShared (M : Program 1) (a b m : OTerm α)
    (one : Nonempty (Derivation body Γ (unary M m a)))
    (two : Nonempty (Derivation body Γ (unary M m b))) :
    Nonempty (Derivation body Γ (accepted (compareMeasurements M) a b)) := by
  apply compositionValue equalityTest ![atSlot M 0,atSlot M 1] (suc z) ![a,b] ![m,m] (equalitySelf m)
  intro k
  exact Fin.cases (slotForward M 0 m ![a,b] one)
    (Fin.cases (slotForward M 1 m ![a,b] two) (fun j => Fin.elim0 j)) k

private theorem sharedReport (M : Program 1) (a b x y : OTerm α)
    (test : Nonempty (Derivation body Γ (programGraph equalityTest (suc z) ![x,y])))
    (one : Nonempty (Derivation body Γ (programGraph (atSlot M 0) x ![a,b])))
    (two : Nonempty (Derivation body Γ (programGraph (atSlot M 1) y ![a,b]))) :
    Nonempty (Derivation body Γ (unary M x a)) ∧ Nonempty (Derivation body Γ (unary M x b)) := by
  obtain ⟨same⟩ := equalityOfAcceptance x y test
  have left : Nonempty (Derivation body Γ (unary M x a)) := slotBackward M 0 x ![a,b] one
  have right : Nonempty (Derivation body Γ (unary M y b)) := slotBackward M 1 y ![a,b] two
  exact ⟨left,outputTransport M y x ![b] ⟨symm same⟩ right⟩

attribute [local irreducible] programGraph in
theorem compareCases (M : Program 1) (a b : OTerm α) (goal : Formula α)
    (compared : Nonempty (Derivation body Γ (accepted (compareMeasurements M) a b)))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (m : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (unary M m (a.relabel j))) →
      Nonempty (Derivation body Δ (unary M m (b.relabel j))) →
      Nonempty (Derivation body Δ (goal.relabel j))) : Nonempty (Derivation body Γ goal) := by
  let calls : Fin 2 → Program 2 := ![atSlot M 0,atSlot M 1]
  let input : Fin 2 → OTerm α := ![a,b]
  have selected : Nonempty (Derivation body Γ (programGraph (.composition equalityTest calls) (suc z) input)) :=
    compared
  have finish (β : Type) (j : α → β) (ys : Fin 2 → OTerm β) (Δ : List (Formula β))
      (hJ : ∀ r ∈ Γ, r.relabel j ∈ Δ)
      (test : Nonempty (Derivation body Δ (programGraph equalityTest ((suc z : OTerm α).relabel j) ys)))
      (components : ∀ i, Nonempty (Derivation body Δ (programGraph (calls i) (ys i)
        (fun k => (input k).relabel j)))) : Nonempty (Derivation body Δ (goal.relabel j)) := by
    have callZero : calls 0 = atSlot M 0 := rfl
    have callOne : calls 1 = atSlot M 1 := rfl
    have first := components 0
    have second := components 1
    rw [callZero] at first
    rw [callOne] at second
    simp only [input,binaryInputsRename] at first second
    have checked : Nonempty (Derivation body Δ (programGraph equalityTest (suc z) ![ys 0,ys 1])) := by
      have tape : ys = ![ys 0,ys 1] := by
        funext i
        refine Fin.cases rfl (fun j => ?_) i
        obtain rfl := Fin.eq_zero j
        rfl
      have guard := test
      rw [sucRelabel,zRelabel] at guard
      rw [← tape]
      exact guard
    obtain ⟨left,right⟩ := sharedReport M (a.relabel j) (b.relabel j) (ys 0) (ys 1) checked first second
    exact use β j Δ (ys 0) hJ left right
  exact programCompositionCases equalityTest calls (suc z) input goal selected finish

end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenCompareProof
