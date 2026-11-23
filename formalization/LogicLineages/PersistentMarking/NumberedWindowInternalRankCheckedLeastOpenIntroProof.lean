module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastOpenIntroProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue outputTransport)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalEqualityTest (predecessor equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalRankCheckedLeast

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem onTape (g : Program 1) (p : Program 3) (xs : Fin 3 → OTerm α) (inTerm out : OTerm α)
    (held : Nonempty (Derivation B Γ (unary g out inTerm)))
    (calls : Nonempty (Derivation B Γ (programGraph p inTerm xs))) :
    Nonempty (Derivation B Γ (programGraph (unaryOn g p) out xs)) := by
  apply compositionValue g (fun _ : Fin 1 => p) out xs ![inTerm] held
  intro j
  obtain rfl := Fin.eq_zero j
  exact calls

/-- A true original successful least and two actual equal-rank reports
install the exact checked-least graph at the same raw seed and result. -/
theorem exact_OpenRankCheckedLeastIntro (g : Program 1) (L : Program 3)
    (ctx ty seed k m : OTerm α)
    (old : Nonempty (Derivation B Γ (programGraph L (suc k) ![ctx,ty,seed])))
    (seedCall : Nonempty (Derivation B Γ (unary g m seed)))
    (outCall : Nonempty (Derivation B Γ (unary g m k))) :
    Nonempty (Derivation B Γ (programGraph (checkedLeast g L) (suc k) ![ctx,ty,seed])) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,seed]
  have source : Nonempty (Derivation B Γ (programGraph (seedRank g) m xs)) :=
    onTape g (.projection 2) xs seed m seedCall (projectionValue 2 xs)
  have prev := onTape predecessor L xs (suc k) k (predecessorSuccessor k) old
  have dst : Nonempty (Derivation B Γ (programGraph (outputRank g L) m xs)) :=
    onTape g (unaryOn predecessor L) xs k m outCall prev
  have same : Nonempty (Derivation B Γ (programGraph (rankEq g L) (suc z) xs)) := by
    apply compositionValue equalityTest
      (Fin.cons (seedRank g) (Fin.cons (outputRank g L) Fin.elim0)) (suc z) xs
      (Fin.cons m (Fin.cons m Fin.elim0)) (equalityOfEqual m m ⟨refl m⟩)
    intro j
    exact Fin.cases source (Fin.cases dst (fun t => Fin.elim0 t)) j
  have okay := conjunctionAccept (rankEq g L) (constantOne 3) xs same (oneConstantValue xs)
  exact successorBranchIntro (rankTest g L) (constantZero 3) L (suc k) z xs okay old

#print axioms exact_OpenRankCheckedLeastIntro
end LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastOpenIntroProof
