module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalPresentationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementObjectTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalPositiveEndpointRefinement (withEndpointCarriers)

/-- A genuine arbitrary-open result from the literal refined positive
program. Recover the actual old r acceptance and the same i graph on
both original endpoints in the same body and hypotheses. No numerical
calibration, shape, typedness, or old-acceptance premise is provided. -/
def ExactOpenPositiveEndpointCarrierGraphs : Prop :=
  ∀ (i : Program 1) (r : Program 3) (B : Positive (Fin 1)) (α : Type)
      (Γ : List (Formula α)) (x w y : OrdinaryArithmetic.Term α),
    let one : OrdinaryArithmetic.Term α := OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm
    Nonempty (Derivation B Γ (programGraph (withEndpointCarriers i r) one ![x,w,y])) →
    Nonempty (Derivation B Γ
      (programGraph r one ![x,w,y] ⊓ (programGraph i one ![x] ⊓ programGraph i one ![y])))

/-- At the actual new source body, the original supplied-certificate
adapter still passes x,w,y to the physical wrapper. The output uses
the two actual new-body scalar formulas and r on that very same tape
under that same new body, not a derivation at the original body. -/
def ExactOriginalPositiveCertificateEndpointCarriers : Prop :=
  ∀ (i j : Program 1) (r d : Program 3) (c : Nat) (α : Type)
      (Γ : List (Formula α)) (x w y : OrdinaryArithmetic.Term α),
    let S := data i j (withEndpointCarriers i r) d
    let B := sourceBody S c
    let one : OrdinaryArithmetic.Term α := OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm
    Nonempty (Derivation B Γ (certificate S false c x y w)) →
    Nonempty (Derivation B Γ
      (programGraph r one ![x,w,y] ⊓ (carrier S false c x ⊓ carrier S false c y)))

end LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementObjectTargets
