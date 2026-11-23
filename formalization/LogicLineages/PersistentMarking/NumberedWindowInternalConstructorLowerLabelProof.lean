module
public import LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLowerLabelTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLowerLabelArithmeticProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLowerLabel
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open ID1Completion.InternalStrongInduction (below)
open ID1Completion.InternalStrongInductionSyntaxProof (belowElimSyntax)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalConstructorLabelStratumTargets (finiteLabelBody)
open NumberedWindowInternalConstructorLowerLabelTargets
open NumberedWindowInternalConstructorLowerLabelArithmeticProof (exactOpenLowerLabel)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem guardResults (guards : List (Program 2)) (xs : Fin 2 → OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph (checkGuards guards) (suc z) xs))) :
    Nonempty (Derivation B Γ (programGraph calledLowerLabel (suc z) xs)) ∧
      ∀ p ∈ guards, Nonempty (Derivation B Γ (programGraph p (suc z) xs)) := by
  induction guards with
  | nil => exact ⟨h,fun _ hm => False.elim (List.not_mem_nil hm)⟩
  | cons p tail ih =>
    obtain ⟨ok⟩ := conjunctionRecover p (checkGuards tail) xs h
    obtain ⟨chosen,rest⟩ := ih ⟨Derivation.conjunctionRight ok⟩
    refine ⟨chosen,?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with he | hm
    · subst q
      exact ⟨Derivation.conjunctionLeft ok⟩
    · exact rest q hm

theorem exactOpenLowerGuards (fit : Program 1) (source destination : OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph (lowerCase fit) (suc z) ![source,destination]))) :
    Nonempty (Derivation B Γ (programGraph calledLowerLabel (suc z) ![source,destination])) ∧
      ∀ p ∈ lowerGuards fit,
        Nonempty (Derivation B Γ (programGraph p (suc z) ![source,destination])) :=
  guardResults (lowerGuards fit) ![source,destination] h

private theorem selector (i : Fin 2) (n : Nat) (xs : Fin 2 → OTerm α) (out : OTerm α)
    (p : Nonempty (Derivation B Γ (unary (field n) out (xs i)))) :
    Nonempty (Derivation B Γ (programGraph (asField i n) out xs)) := by
  apply compositionValue (field n) ![.projection i] out xs ![xs i] p
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue i xs

theorem exactOpenLowerUse : ExactOpenLowerUse := by
  intro fit B α Γ source destination src dst finite held a b smaller
  let xs : Fin 2 → OTerm α := ![source,destination]
  have called := (exactOpenLowerGuards fit source destination held).1
  have run : Nonempty (Derivation B Γ (programGraph lowerLabel (suc z) ![src,dst])) := by
    apply compositionRecover lowerLabel ![asField 0 2,asField 1 2] (suc z) xs ![src,dst] called
    intro i
    exact Fin.cases (selector 0 2 xs src a) (Fin.cases (selector 1 2 xs dst b)
      (fun j => Fin.elim0 j)) i
  obtain ⟨o⟩ := exactOpenLowerLabel B α Γ src dst run
  obtain ⟨h⟩ := smaller
  unfold below at h
  have deduct := Derivation.universalElimination (emb dst) h
  rw [belowElimSyntax] at deduct
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft o)
    (Derivation.implicationElimination deduct (Derivation.conjunctionRight o))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLowerLabel
