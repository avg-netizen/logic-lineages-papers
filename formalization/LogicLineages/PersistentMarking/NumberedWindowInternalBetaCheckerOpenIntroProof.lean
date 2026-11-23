module
public import LogicLineages.PersistentMarking.NumberedWindowInternalBetaSubDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalBetaCheckerOpenIntroProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue successorValue)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalBetaSub (betaChecker)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem binaryValue {n : Nat} (P : Program 2) (a b : Program n)
    (out x y : OTerm α) (xs : Fin n → OTerm α)
    (call : Nonempty (Derivation B Γ (programGraph P out ![x,y])))
    (left : Nonempty (Derivation B Γ (programGraph a x xs)))
    (right : Nonempty (Derivation B Γ (programGraph b y xs))) :
    Nonempty (Derivation B Γ (programGraph (.composition P ![a,b]) out xs)) := by
  apply compositionValue P (Fin.cons a (Fin.cons b Fin.elim0)) out xs ![x,y] call
  intro i
  exact Fin.cases left (Fin.cases right (fun j => Fin.elim0 j)) i

private theorem targetValue (src dst : OTerm α) :
    Nonempty (Derivation B Γ (programGraph
      (.composition .succ (fun _ : Fin 1 => .projection (1 : Fin 2))) (suc dst) ![src,dst])) := by
  let ys : Fin 1 → OTerm α := fun _ => dst
  apply compositionValue .succ (fun _ : Fin 1 => .projection (1 : Fin 2))
    (suc dst) ![src,dst] ys (successorValue ys)
  intro _
  exact projectionValue (1 : Fin 2) ![src,dst]

/-- Genuinely open ID₁ acceptance from the three physical decoder reports
and an actual successful substitution call, with no numeral evaluation. -/
theorem accept (guard arg body sub : Program 2) (src dst a v : OTerm α)
    (valid : Nonempty (Derivation B Γ (programGraph guard (suc z) ![src,dst])))
    (argRead : Nonempty (Derivation B Γ (programGraph arg a ![src,dst])))
    (bodyRead : Nonempty (Derivation B Γ (programGraph body v ![src,dst])))
    (result : Nonempty (Derivation B Γ (programGraph sub (suc dst) ![a,v]))) :
    Nonempty (Derivation B Γ (programGraph (betaChecker guard arg body sub) (suc z) ![src,dst])) := by
  have selected := binaryValue sub arg body (suc dst) a v ![src,dst] result argRead bodyRead
  have compare := binaryValue equalityTest (.composition sub ![arg,body])
    (.composition .succ (fun _ : Fin 1 => .projection (1 : Fin 2)))
    (suc z) (suc dst) (suc dst) ![src,dst] (equalitySelf (suc dst)) selected (targetValue src dst)
  exact successorBranchIntro guard (constantZero 2) _ (suc z) z ![src,dst] valid compare

#print axioms accept
end LogicLineages.PersistentMarking.NumberedWindowInternalBetaCheckerOpenIntroProof
