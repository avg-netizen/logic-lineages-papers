module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalListCodec InternalGraphComposition

/-- Introduction uses an actual original pair-graph witness at arbitrary terms. -/
def ActualOriginalConsIntroduction : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (p h t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((programGraph InternalPairing.pairing p (Fin.cons h (Fin.cons t Fin.elim0))).imp
      (programGraph consCode (OrdinaryArithmetic.succTerm p) (Fin.cons h (Fin.cons t Fin.elim0)))))

/-- Every generated cons has its actual head/tail and is not the nil code. -/
def ActualOriginalConsDestruction : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n h t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((programGraph consCode n (Fin.cons h (Fin.cons t Fin.elim0))).imp
      ((programGraph headCode h (Fin.cons n Fin.elim0)) ⊓
       ((programGraph tailCode t (Fin.cons n Fin.elim0)) ⊓
        (equal n OrdinaryArithmetic.zeroTerm).not))))

/-- Arbitrary outputs of the literal destructor graphs are the original fields. -/
def ActualOriginalConsDestructorEquations : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n h t a b : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    (((programGraph consCode n (Fin.cons h (Fin.cons t Fin.elim0))) ⊓
      ((programGraph headCode a (Fin.cons n Fin.elim0)) ⊓
       (programGraph tailCode b (Fin.cons n Fin.elim0)))).imp
      ((equal a h) ⊓ (equal b t))))

/-- Injectivity is an object-calculus consequence of the generated-code inverse. -/
def ActualOriginalConsInjectivity : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n h t h' t' : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    (((programGraph consCode n (Fin.cons h (Fin.cons t Fin.elim0))) ⊓
      (programGraph consCode n (Fin.cons h' (Fin.cons t' Fin.elim0)))).imp
      ((equal h h') ⊓ (equal t t'))))

/-- Exact zero/one nil-test equation, including rejection of every nonzero code. -/
def ActualOriginalNilTestGraph : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (out n : OrdinaryArithmetic.Term α),
  let g := programGraph nilTest out (Fin.cons n Fin.elim0)
  let s := testSpec out n OrdinaryArithmetic.zeroTerm
  Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g)))

def ActualOriginalListCodecTotalFunctional : Prop :=
  ∀ body : Positive (Fin 1),
  (Total body (OrdinaryArithmetic.graphFormula consCode) ∧
   Functional body (OrdinaryArithmetic.graphFormula consCode)) ∧
  (Total body (OrdinaryArithmetic.graphFormula headCode) ∧
   Functional body (OrdinaryArithmetic.graphFormula headCode)) ∧
  (Total body (OrdinaryArithmetic.graphFormula tailCode) ∧
   Functional body (OrdinaryArithmetic.graphFormula tailCode)) ∧
  (Total body (OrdinaryArithmetic.graphFormula nilTest) ∧
   Functional body (OrdinaryArithmetic.graphFormula nilTest))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecTargets
