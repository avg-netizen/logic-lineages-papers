module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsArithmeticProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairOrderProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans cancelSuc sucNeZeroApply)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalAdditionCancellationProof (leftCancellation)
open ID1Completion.InternalMultiplicationLawsProof (congAddRight)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalSquareRootArithmetic (square interval)
open ID1Completion.InternalSquareRootArithmeticSupportProof (squareCongr orderRight)
open ID1Completion.InternalSquareRootArithmeticProof (intervalUnique)
open ID1Completion.InternalUnpairArithmeticProof (leftWeakAdd offsetInterval intervalInputTransport)
open ID1Completion.InternalUnpairReverseBoundsArithmeticProof (rightWeakAdd weakTrans squareSelfWeak)
open NumberedWindowInternalSparsePair (pairTerm fieldCons)
open NumberedWindowInternalSparsePairTargets NumberedWindowInternalSparsePairGraphProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem exactInterval (x y : OTerm α) :
    Nonempty (Derivation body Γ (interval (add x y) (pairTerm x y))) := by
  let s := add x y
  exact offsetInterval s x (weakTrans x s (add s s) (leftWeakAdd x y) (leftWeakAdd s s))

private theorem coordinateEquality (x y u v : OTerm α)
    (h : Derivation body Γ (eqn (pairTerm x y) (pairTerm u v))) :
    Nonempty (Derivation body Γ (eqn x u ⊓ eqn y v)) := by
  let s := add x y
  let t := add u v
  obtain ⟨intervalLeft⟩ := exactInterval (body := body) (Γ := Γ) x y
  obtain ⟨intervalRight⟩ := exactInterval (body := body) (Γ := Γ) u v
  obtain ⟨sums⟩ := intervalUnique s t (pairTerm x y) ⟨intervalLeft⟩
    ⟨intervalInputTransport t (symm h) intervalRight⟩
  have moved : Derivation body Γ (eqn (add (square t) u) (add (square s) u)) :=
    congAddRight u (squareCongr (symm sums))
  have left : Derivation body Γ (eqn x u) :=
    Derivation.implicationElimination (leftCancellation x u (square s)) (trans h moved)
  have right : Derivation body Γ (eqn y v) :=
    Derivation.implicationElimination (leftCancellation y v x)
      (trans sums (congAddRight v (symm left)))
  exact ⟨Derivation.conjunctionIntroduction left right⟩

theorem pairInjective : OpenPairInjective := by
  intro body α out x y u v
  simp only [equalEqn]
  let g := programGraph NumberedWindowInternalSparsePair.pair out ![x,y] ⊓
    programGraph NumberedWindowInternalSparsePair.pair out ![u,v]
  have both : Derivation body [g] g := Derivation.hypothesis List.mem_cons_self
  obtain ⟨one⟩ := pairEquation out x y ⟨Derivation.conjunctionLeft both⟩
  obtain ⟨two⟩ := pairEquation out u v ⟨Derivation.conjunctionRight both⟩
  obtain ⟨components⟩ := coordinateEquality x y u v (trans (symm one) two)
  exact ⟨Derivation.implicationIntroduction components⟩

theorem consInjective : OpenFieldConsInjective := by
  intro body α out x y u v
  simp only [equalEqn]
  let g := programGraph fieldCons out ![x,y] ⊓ programGraph fieldCons out ![u,v]
  have both : Derivation body [g] g := Derivation.hypothesis List.mem_cons_self
  obtain ⟨one⟩ := consEquation out x y ⟨Derivation.conjunctionLeft both⟩
  obtain ⟨two⟩ := consEquation out u v ⟨Derivation.conjunctionRight both⟩
  obtain ⟨components⟩ := coordinateEquality x y u v (cancelSuc (trans (symm one) two))
  exact ⟨Derivation.implicationIntroduction components⟩

theorem consTailDecrease : OpenFieldConsTailDecrease := by
  intro body α out x tail
  simp only [equalEqn]
  let g := programGraph fieldCons out ![x,tail]
  let s := add x tail
  obtain ⟨e⟩ := consEquation (body := body) (Γ := [g]) out x tail
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have nz : Derivation body [g] (eqn out z).not := by
    apply Derivation.implicationIntroduction
    exact sucNeZeroApply (trans (symm (addHyp e (eqn out z))) (Derivation.hypothesis List.mem_cons_self))
  obtain ⟨lt⟩ := weakTrans (body := body) (Gamma := [g]) tail (square s) (pairTerm x tail)
    (weakTrans tail s (square s) (rightWeakAdd x tail) (squareSelfWeak s))
    (leftWeakAdd (square s) x)
  exact ⟨Derivation.implicationIntroduction
    (Derivation.conjunctionIntroduction nz (orderRight tail (symm e) lt))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairOrderProof
