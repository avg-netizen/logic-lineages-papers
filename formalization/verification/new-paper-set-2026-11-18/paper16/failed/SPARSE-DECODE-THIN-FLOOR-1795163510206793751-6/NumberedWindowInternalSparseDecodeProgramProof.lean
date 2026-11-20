module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsMultiplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestSubtractionSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeProgramProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalArithmeticProgramsMultiplicationProof (multiplicationValue)
open ID1Completion.InternalEqualityTestSubtractionSupportProof (subGraph)
open ID1Completion.InternalSquareRoot (root)
open ID1Completion.InternalSquareRootArithmetic (square)
open ID1Completion.InternalArithmeticPrograms (multiplication)
open ID1Completion.InternalEqualityTest (subtract)
open NumberedWindowInternalSparseDecode NumberedWindowInternalSparseDecodeSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem rootSquareGraph (n s : OTerm α) (hs : Nonempty (Derivation body Γ (unary root s n))) :
    Nonempty (Derivation body Γ (unary rootSquare (square s) n)) := by
  apply compositionValue multiplication ![root,root] (square s) ![n] ![s,s] (multiplicationValue s s)
  intro i
  exact Fin.cases hs (Fin.cases hs (fun k => Fin.elim0 k)) i

theorem leftGraph (n s x : OTerm α)
    (hs : Nonempty (Derivation body Γ (unary root s n)))
    (h : Nonempty (Derivation body Γ (subGraph x (square s) n))) :
    Nonempty (Derivation body Γ (unary leftCandidate x n)) := by
  apply compositionValue subtract ![rootSquare,.projection 0] x ![n] ![square s,n] h
  intro i
  exact Fin.cases (rootSquareGraph n s hs) (Fin.cases (projectionValue (0 : Fin 1) ![n])
    (fun k => Fin.elim0 k)) i

theorem leftInversion (n s x : OTerm α)
    (hs : Nonempty (Derivation body Γ (unary root s n)))
    (h : Nonempty (Derivation body Γ (unary leftCandidate x n))) :
    Nonempty (Derivation body Γ (subGraph x (square s) n)) := by
  apply compositionRecover subtract ![rootSquare,.projection 0] x ![n] ![square s,n] h
  intro i
  exact Fin.cases (rootSquareGraph n s hs) (Fin.cases (projectionValue (0 : Fin 1) ![n])
    (fun k => Fin.elim0 k)) i

theorem rightGraph (n s x y : OTerm α)
    (hs : Nonempty (Derivation body Γ (unary root s n)))
    (hx : Nonempty (Derivation body Γ (unary leftCandidate x n)))
    (h : Nonempty (Derivation body Γ (subGraph y x s))) :
    Nonempty (Derivation body Γ (unary rightCandidate y n)) := by
  apply compositionValue subtract ![leftCandidate,root] y ![n] ![x,s] h
  intro i
  exact Fin.cases hx (Fin.cases hs (fun k => Fin.elim0 k)) i

theorem rightInversion (n s x y : OTerm α)
    (hs : Nonempty (Derivation body Γ (unary root s n)))
    (hx : Nonempty (Derivation body Γ (unary leftCandidate x n)))
    (h : Nonempty (Derivation body Γ (unary rightCandidate y n))) :
    Nonempty (Derivation body Γ (subGraph y x s)) := by
  apply compositionRecover subtract ![leftCandidate,root] y ![n] ![x,s] h
  intro i
  exact Fin.cases hx (Fin.cases hs (fun k => Fin.elim0 k)) i

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeProgramProof
