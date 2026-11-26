module

public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombinePairProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue)
open ID1Completion.InternalArithmeticProgramsSupportProof (additionValue)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalUnpairProof (actualOriginalGeneratedCodeInverse)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalChosenAuxMeasureCombine
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem oneGraph {n : Nat} (p : Program 1) (q : Program n) (out val : OTerm α) (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Γ (programGraph p out ![val])))
    (hq : Nonempty (Derivation body Γ (programGraph q val xs))) :
    Nonempty (Derivation body Γ (programGraph (callOne p q) out xs)) := by
  apply compositionValue p (fun _ : Fin 1 => q) out xs ![val] hp
  intro i
  obtain rfl := Fin.eq_zero i
  exact hq

private theorem selectors {n : Nat} (a b : Program n) (x y : OTerm α) (xs : Fin n → OTerm α)
    (ha : Nonempty (Derivation body Γ (programGraph a x xs)))
    (hb : Nonempty (Derivation body Γ (programGraph b y xs))) (i : Fin 2) :
    Nonempty (Derivation body Γ (programGraph ((![a,b] : Fin 2 → Program n) i) ((![x,y] : Fin 2 → OTerm α) i) xs)) :=
  Fin.cases ha (Fin.cases hb (fun j => Fin.elim0 j)) i

private theorem twoGraph {n : Nat} (p : Program 2) (a b : Program n) (out x y : OTerm α)
    (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Γ (programGraph p out ![x,y])))
    (ha : Nonempty (Derivation body Γ (programGraph a x xs)))
    (hb : Nonempty (Derivation body Γ (programGraph b y xs))) :
    Nonempty (Derivation body Γ (programGraph (callTwo p a b) out xs)) :=
  compositionValue p ![a,b] out xs ![x,y] hp (selectors a b x y xs ha hb)

private theorem field (p : Program 1) (i : Fin 2) (v : OTerm α) (xs : Fin 2 → OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph p v ![xs i]))) :
    Nonempty (Derivation body Γ (programGraph (coordinate p i) v xs)) :=
  oneGraph p (.projection i) v (xs i) xs h (projectionValue i xs)

/-- Recover the actual terminal pairing from the very same combine graph
and a genuine report of its physical max call. -/
theorem pairFromCombine (p mf ma df da bf ba b : OTerm α)
    (hf : Nonempty (Derivation body Γ (codePair mf df bf)))
    (ha : Nonempty (Derivation body Γ (codePair ma da ba)))
    (out : Nonempty (Derivation body Γ (programGraph chosenCombine p ![mf,ma])))
    (largest : Nonempty (Derivation body Γ (programGraph maximum b ![bf,ba]))) :
    Nonempty (Derivation body Γ (codePair p (suc (add df da)) b)) := by
  let L := ID1Completion.InternalUnpair.left
  let R := ID1Completion.InternalUnpair.right
  let xs : Fin 2 → OTerm α := ![mf,ma]
  obtain ⟨leftLaw⟩ := actualOriginalGeneratedCodeInverse body α mf df bf
  obtain ⟨rightLaw⟩ := actualOriginalGeneratedCodeInverse body α ma da ba
  obtain ⟨hf⟩ := hf
  obtain ⟨ha⟩ := ha
  have fFields := Derivation.implicationElimination (weakenClosed leftLaw Γ) hf
  have aFields := Derivation.implicationElimination (weakenClosed rightLaw Γ) ha
  have sum : Nonempty (Derivation body Γ (programGraph predecessorDepth (add df da) xs)) :=
    twoGraph ID1Completion.InternalArithmeticPrograms.addition (coordinate L 0) (coordinate L 1)
      (add df da) df da xs (additionValue df da)
      (field L 0 df xs ⟨Derivation.conjunctionLeft fFields⟩)
      (field L 1 da xs ⟨Derivation.conjunctionLeft aFields⟩)
  have depth : Nonempty (Derivation body Γ (programGraph (callOne .succ predecessorDepth) (suc (add df da)) xs)) :=
    oneGraph .succ predecessorDepth (suc (add df da)) (add df da) xs (successorValue ![add df da]) sum
  have numerals : Nonempty (Derivation body Γ (programGraph numeralBound b xs)) :=
    twoGraph maximum (coordinate R 0) (coordinate R 1) b bf ba xs largest
      (field R 0 bf xs ⟨Derivation.conjunctionRight fFields⟩)
      (field R 1 ba xs ⟨Derivation.conjunctionRight aFields⟩)
  exact compositionRecover ID1Completion.InternalPairing.pairing
    ![callOne .succ predecessorDepth,numeralBound] p xs ![suc (add df da),b] out
    (selectors (callOne .succ predecessorDepth) numeralBound (suc (add df da)) b xs depth numerals)

end LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombinePairProof
