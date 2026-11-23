module
public import LogicLineages.PersistentMarking.NumberedWindowInternalConstructorOmegaMarkTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalConstructorOmegaMarkProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalConstructorOmegaMarkTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem reports (guards : List (Program 3)) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph (checkGuards guards) (suc z) xs))) :
    Nonempty (Derivation B Γ (programGraph markLabel (suc z) xs)) ∧
      ∀ p ∈ guards, Nonempty (Derivation B Γ (programGraph p (suc z) xs)) := by
  induction guards with
  | nil => exact ⟨h,fun _ hm => False.elim (List.not_mem_nil hm)⟩
  | cons h₀ tail ih =>
    obtain ⟨ok⟩ := conjunctionRecover h₀ (checkGuards tail) xs h
    obtain ⟨found,rest⟩ := ih ⟨Derivation.conjunctionRight ok⟩
    refine ⟨found,?_⟩
    intro p hm
    rcases List.mem_cons.mp hm with eq | ht
    · subst p
      exact ⟨Derivation.conjunctionLeft ok⟩
    · exact rest p ht

theorem exact_OpenOmegaMarkGuards (fit decl : Program 1) (label source target : OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph (markCase fit decl) (suc z) ![label,source,target]))) :
    Nonempty (Derivation B Γ (programGraph markLabel (suc z) ![label,source,target])) ∧
      ∀ p ∈ markGuards fit decl,
        Nonempty (Derivation B Γ (programGraph p (suc z) ![label,source,target])) :=
  reports (markGuards fit decl) ![label,source,target] h

private theorem markEquality (label source target selected : OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph markLabel (suc z) ![label,source,target])))
    (v : Nonempty (Derivation B Γ (unary (field 2) selected target))) :
    Nonempty (Derivation B Γ (eqn label selected)) := by
  let xs : Fin 3 → OTerm α := ![label,source,target]
  have fieldReport : Nonempty (Derivation B Γ (programGraph (fieldAt 2 2) selected xs)) := by
    apply compositionValue (field 2) ![.projection 2] selected xs ![target] v
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 2 xs
  have tested : Nonempty (Derivation B Γ (programGraph equalityTest (suc z) ![label,selected])) := by
    apply compositionRecover equalityTest ![.projection 0,fieldAt 2 2]
      (suc z) xs ![label,selected] h
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases fieldReport (fun k => Fin.elim0 k)) i
  exact equalityOfAcceptance label selected tested

theorem exact_OpenOmegaMarkUse : ExactOpenOmegaMarkUse := by
  intro fit decl B α Γ label source destination selected finite h fields paid
  obtain ⟨eq⟩ := markEquality label source destination selected
    (exact_OpenOmegaMarkGuards fit decl label source destination h).1 fields
  obtain ⟨closed⟩ := paid
  exact ⟨Derivation.conjunctionIntroduction eq (Derivation.universalElimination (emb selected) closed)⟩

#print axioms exact_OpenOmegaMarkGuards
#print axioms exact_OpenOmegaMarkUse
end LogicLineages.PersistentMarking.NumberedWindowInternalConstructorOmegaMarkProof
