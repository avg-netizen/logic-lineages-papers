module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryTargets
open Source NumberedRewriteReduction NumberedAuxiliaryCoding NumberedUniformPackedDecoding
open ID1Completion.ContextUniformPrimary

def ActualRawClassCodesCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q : Packed (Fin n) arity Gamma),
  classCodes arity symbols S Gamma (packedCode q) = NumberedAuxiliaryEnumeration.classCodes symbols S q

def ActualRawPrimaryListCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q : Packed (Fin n) arity Gamma),
  primaryList arity symbols S Gamma (packedCode q) =
    (NumberedPrimaryClassPrimrec.primaryList symbols S q).map packedCode

def ActualRawPrimaryTestCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q r : Packed (Fin n) arity Gamma),
  primaryTest arity symbols S Gamma (packedCode q) (packedCode r) =
    NumberedFinitePrimaryClass.primaryTest symbols S q r

def ActualRawRepresentativeCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q : Packed (Fin n) arity Gamma),
  representative arity symbols S Gamma (packedCode q) =
    NumberedLeastCodeRepresentative.representativeCode symbols S q

def ActualRawPrimaryPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun p : Window n × List Ty × RawPacked n × RawPacked n =>
    primaryTest arity p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2)

def ActualRawRepresentativePrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun p : Window n × List Ty × RawPacked n =>
    representative arity p.1.1 p.1.2 p.2.1 p.2.2)

def ActualUniformCanonicalPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun p : Window n × List Ty × Nat =>
    canonicalCarrier n arity p.1.1 p.1.2 p.2.1 p.2.2)

def ActualUniformCanonicalCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty) (value : Nat),
  canonicalCarrier n arity symbols S Gamma value =
    NumberedNumericCarrier.canonicalCarrierTest n arity symbols S Gamma value

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryTargets
