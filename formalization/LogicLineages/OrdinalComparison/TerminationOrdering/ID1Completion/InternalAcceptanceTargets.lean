module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open InternalControlGraph InternalAcceptance
open LogicLineages.ComputabilityKnowledge GorbowPRProgram

/-- Same arbitrary Program and symbolic inputs on each side, accepted exactly at ONE. -/
def ActualOriginalNormalizationAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (n : Nat) (p : Program n) (α : Type)
    (xs : Fin n → OTerm α),
  let one := OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm
  let g := programGraph (GorbowVerifierNormalization.normalize p) one xs
  let s := programGraph p one xs
  Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g)))

def ActualOriginalConjunctionAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (n : Nat) (p q : Program n) (α : Type)
    (xs : Fin n → OTerm α),
  let one := OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm
  let g := programGraph (conjunction p q) one xs
  let s := programGraph p one xs ⊓ programGraph q one xs
  Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g)))

/-- Natural evaluation is calibration only, never reflected into Derivation. -/
def ActualConjunctionEvaluation : Prop :=
  ∀ (n : Nat) (p q : Program n) (xs : List.Vector Nat n),
  evaluate (conjunction p q) xs =
    if evaluate p xs = 1 ∧ evaluate q xs = 1 then 1 else 0

/-- Internal control premises select the actual wrapper, with symbolic output. -/
def ActualOriginalZeroBranch : Prop :=
  ∀ (body : Positive (Fin 1)) (n : Nat) (control a b : Program n) (α : Type)
    (out : OTerm α) (xs : Fin n → OTerm α),
  let g := programGraph (branch control a b) out xs
  let s := programGraph a out xs
  Nonempty (Derivation body [] ((programGraph control OrdinaryArithmetic.zeroTerm xs).imp
    ((g.imp s) ⊓ (s.imp g))))

def ActualOriginalSuccessorBranch : Prop :=
  ∀ (body : Positive (Fin 1)) (n : Nat) (control a b : Program n) (α : Type)
    (out k : OTerm α) (xs : Fin n → OTerm α),
  let g := programGraph (branch control a b) out xs
  let s := programGraph b out xs
  Nonempty (Derivation body [] ((programGraph control (OrdinaryArithmetic.succTerm k) xs).imp
    ((g.imp s) ⊓ (s.imp g))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceTargets
