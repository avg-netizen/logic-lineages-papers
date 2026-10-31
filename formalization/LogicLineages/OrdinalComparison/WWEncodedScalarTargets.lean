module
public import LogicLineages.OrdinalComparison.WWEncodedScalarDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open ForwardTranslation

def ScalarCodeInstantiationPrimitiveRecursive : Prop :=
  Primrec (fun p : Nat × List Nat => instantiateScalarCode p.2 p.1)

def ScalarCodeInstantiationCorrect : Prop :=
  ∀ (ι : Type) (index : ι → Nat) (s : Scalar ι) (xs : List Nat),
    instantiateScalarCode xs (scalarCode index s) = positiveExprEncode (scalarGround index xs s)

def EncodedScalarComputable : Prop :=
  Computable (fun p : Nat × List Nat => encodedScalarValue p.1 p.2)

def EncodedScalarSourceCorrect : Prop :=
  ∀ (ι : Type) (index : ι → Nat) (s : Scalar ι) (xs : List Nat),
    encodedScalarValue (scalarCode index s) xs = s.value (fun i => xs.getD (index i) 0 + 1)
end LogicLineages.OrdinalComparison.Source.Targets
