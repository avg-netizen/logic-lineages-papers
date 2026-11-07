module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalListCodec

/-- Every nonzero input is reconstructed from its actual original destructor
graphs. There is no canonicality premise or assumed decoded list. -/
def ActualOriginalNonzeroListReconstruction : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n h t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    (((equal n OrdinaryArithmetic.zeroTerm).not ⊓
      ((programGraph headCode h (Fin.cons n Fin.elim0)) ⊓
       (programGraph tailCode t (Fin.cons n Fin.elim0)))).imp
      (programGraph consCode n (Fin.cons h (Fin.cons t Fin.elim0)))))

/-- The original tail graph strictly decreases every nonzero input. A head
graph or external successful-decoding hypothesis is deliberately unnecessary. -/
def ActualOriginalNonzeroTailDescent : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    (((equal n OrdinaryArithmetic.zeroTerm).not ⊓
      (programGraph tailCode t (Fin.cons n Fin.elim0))).imp
      (InternalLessThan.strictLess t n)))

/-- Constructor-oriented form of the same strict original list-tail descent. -/
def ActualOriginalConsTailDescent : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n h t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((programGraph consCode n (Fin.cons h (Fin.cons t Fin.elim0))).imp
      (InternalLessThan.strictLess t n)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionTargets
