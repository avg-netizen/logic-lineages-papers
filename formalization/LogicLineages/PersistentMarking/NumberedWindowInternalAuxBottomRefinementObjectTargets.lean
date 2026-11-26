module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementObjectTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm sourceFields)
open NumberedWindowInternalAtomicApplicationShapeObjectTargets (auxAddressTerm bottomTerm)
open NumberedWindowInternalAuxBottomRefinement

def packedAuxBottomTerm {α : Type} (c domain codomain stored arg : OTerm α) : OTerm α :=
  auxAddressTerm c domain codomain (bottomTerm stored) arg

/-- A given literal original packed aux-bottom source enables the
physical recognizer and exact actual source fields c/codomain. -/
def ExactOpenAuxBottomRecognition : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (x c domain codomain stored arg : OTerm α),
    Nonempty (Derivation B Γ (equal x (packedAuxBottomTerm c domain codomain stored arg))) →
    Nonempty (Derivation B Γ (programGraph sourceFlag (numeral 1) ![x] ⊓ sourceFields x c codomain))

/-- Same literal x and actual w,y in the new checker. Extract the
whole bottom equation and genuine actual i graph, in arbitrary open
arithmetic, independently of numerical source calibration. -/
def ExactOpenAuxBottomTerminal : Prop :=
  ∀ (i : Program 1) (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (x w y c domain codomain stored arg : OTerm α),
    Nonempty (Derivation B Γ (equal x (packedAuxBottomTerm c domain codomain stored arg))) →
    Nonempty (Derivation B Γ (programGraph (refineAuxBottom i r) (numeral 1) ![x,w,y])) →
    Nonempty (Derivation B Γ
      (equal y (packedBottomTerm c codomain) ⊓ programGraph i (numeral 1) ![y]))

/-- Actual new acceptance implies actual old r acceptance on the same
physical three claims under the SAME arbitrary arithmetic body. -/
def ExactOpenAuxBottomForgets : Prop :=
  ∀ (i : Program 1) (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (x w y : OTerm α),
    Nonempty (Derivation B Γ (programGraph (refineAuxBottom i r) (numeral 1) ![x,w,y])) →
    Nonempty (Derivation B Γ (programGraph r (numeral 1) ![x,w,y]))

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementObjectTargets
