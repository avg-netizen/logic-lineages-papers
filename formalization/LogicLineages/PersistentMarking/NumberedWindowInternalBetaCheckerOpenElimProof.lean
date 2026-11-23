module
public import LogicLineages.PersistentMarking.NumberedWindowInternalBetaCheckerOpenIntroProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalBetaCheckerOpenElimProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (trans)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (programCases programCompositionCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof
  (projectionValue compositionValue successorValue valueUnique outputTransport programRename)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalBetaSub (betaChecker)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private def target : Program 2 :=
  .composition .succ (fun _ : Fin 1 => .projection (1 : Fin 2))

private theorem targetReport (src dst : OTerm α) :
    Nonempty (Derivation B Γ (programGraph target (suc dst) ![src,dst])) := by
  let ys : Fin 1 → OTerm α := fun _ => dst
  unfold target
  apply compositionValue .succ (fun _ : Fin 1 => .projection (1 : Fin 2))
    (suc dst) ![src,dst] ys (successorValue ys)
  intro _
  exact projectionValue (1 : Fin 2) ![src,dst]

private theorem recoverOutput (arg body sub : Program 2) (src dst : OTerm α)
    (yes : Nonempty (Derivation B Γ (programGraph
      (.composition equalityTest ![.composition sub ![arg,body],target]) (suc z) ![src,dst]))) :
    Nonempty (Derivation B Γ (programGraph (.composition sub ![arg,body]) (suc dst) ![src,dst])) := by
  apply programCompositionCases equalityTest ![.composition sub ![arg,body],target]
    (suc z) ![src,dst] _ yes
  intro β j ys Δ _ eq parts
  simp only [sucRelabel,zRelabel] at eq
  simp only [programRename,sucRelabel]
  let xs : Fin 2 → OTerm β := ![src.relabel j,dst.relabel j]
  have xsRelabel : xs = (fun i : Fin 2 => (![src,dst] i).relabel j) := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · rfl
    · have hk : k = 0 := Fin.eq_zero k
      subst k
      rfl
  rw [← xsRelabel] at parts ⊢
  have first : Nonempty (Derivation B Δ (programGraph (.composition sub ![arg,body]) (ys 0) xs)) :=
    parts 0
  have second : Nonempty (Derivation B Δ (programGraph target (ys 1) xs)) := parts 1
  have ysTuple : (![ys 0,ys 1] : Fin 2 → OTerm β) = ys := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · rfl
    · have hk : k = 0 := Fin.eq_zero k
      subst k
      rfl
  have acceptEq : Nonempty (Derivation B Δ
      (ID1Completion.InternalEqualityTestCompositionProof.equalityGraph (suc z) (ys 0) (ys 1))) := by
    change Nonempty (Derivation B Δ (programGraph equalityTest (suc z) ![ys 0,ys 1]))
    rw [ysTuple]
    exact eq
  have hit := equalityOfAcceptance (ys 0) (ys 1) acceptEq
  obtain ⟨same⟩ := valueUnique target (ys 1) (suc (dst.relabel j)) xs second
    (targetReport (src.relabel j) (dst.relabel j))
  obtain ⟨e⟩ := hit
  exact outputTransport (.composition sub ![arg,body]) (ys 0) (suc (dst.relabel j)) xs
    ⟨trans e same⟩ first

/-- Converse in the actual open calculus, with a known nonzero guard value.
The numeric calibration of the selected guard is not used as a reflection rule. -/
theorem substitution (guard arg body sub : Program 2) (src dst a v k : OTerm α)
    (valid : Nonempty (Derivation B Γ (programGraph guard (suc k) ![src,dst])))
    (argRead : Nonempty (Derivation B Γ (programGraph arg a ![src,dst])))
    (bodyRead : Nonempty (Derivation B Γ (programGraph body v ![src,dst])))
    (yes : Nonempty (Derivation B Γ (programGraph (betaChecker guard arg body sub) (suc z) ![src,dst]))) :
    Nonempty (Derivation B Γ (programGraph sub (suc dst) ![a,v])) := by
  have compared := successorBranchElim guard (constantZero 2)
    (.composition equalityTest ![.composition sub ![arg,body],target])
    (suc z) k ![src,dst] valid yes
  apply compositionRecover sub ![arg,body] (suc dst) ![src,dst] ![a,v]
    (recoverOutput arg body sub src dst compared)
  intro i
  exact Fin.cases argRead (Fin.cases bodyRead (fun j => Fin.elim0 j)) i

#print axioms substitution
end LogicLineages.PersistentMarking.NumberedWindowInternalBetaCheckerOpenElimProof
