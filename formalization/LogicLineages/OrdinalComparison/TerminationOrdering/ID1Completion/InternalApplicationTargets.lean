module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplication
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualOriginalActiveGraph : Prop :=
  ∀ (body : Positive (Fin 1)) (active result : Program 5) (old : Program 6)
    (α : Type) (xs : Fin 5 → OTerm α) (out : OTerm α),
  let one := OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm
  let premise := programGraph active one xs
  let g := programGraph (application active result old) one (inputs xs out)
  let s := programGraph result out xs
  Nonempty (Derivation body [] (premise.imp ((g.imp s) ⊓ (s.imp g))))

def ActualOriginalInactiveGraph : Prop :=
  ∀ (body : Positive (Fin 1)) (active result : Program 5) (old : Program 6)
    (α : Type) (xs : Fin 5 → OTerm α) (out value : OTerm α),
  let premise := programGraph active OrdinaryArithmetic.zeroTerm xs
  let g := programGraph (application active result old) value (inputs xs out)
  let s := programGraph old value (inputs xs out)
  Nonempty (Derivation body [] (premise.imp ((g.imp s) ⊓ (s.imp g))))

def ActualOriginalActiveTotality : Prop :=
  ∀ (body : Positive (Fin 1)) (active result : Program 5) (old : Program 6)
    (α : Type) (xs : Fin 5 → OTerm α),
  Nonempty (Derivation body []
    ((programGraph active (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) xs).imp
      (applicationExists (application active result old) xs)))

/-- Equality of accepted RAW result codes in the original object calculus. -/
def ActualOriginalActiveFunctionality : Prop :=
  ∀ (body : Positive (Fin 1)) (active result : Program 5) (old : Program 6)
    (α : Type) (xs : Fin 5 → OTerm α) (out other : OTerm α),
  let one := OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm
  let p := application active result old
  Nonempty (Derivation body [] ((programGraph active one xs).imp
    ((programGraph p one (inputs xs out) ⊓ programGraph p one (inputs xs other)).imp
      (equal out other))))

/-- Exact all-input calibration; symbolic derivations are separate targets. -/
def ActualCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (old : JointGammaComputability.Data)
    (window : Program 1) (arrow : Program 2) (result : Program 5),
  JointGammaComputability.Calibrated old n arity →
  (∀ v, evaluate window v = GuardCalibration.validWindowValue n v) →
  (∀ v, evaluate arrow v = ApplicationDomain.arrowValue v) →
  (∀ v, evaluate result v = ApplicationResultBuilder.resultValue n arity v) →
  JointGammaComputability.Calibrated (computability old window arrow result) n arity

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationTargets
