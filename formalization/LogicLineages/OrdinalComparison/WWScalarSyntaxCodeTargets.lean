module
public import LogicLineages.OrdinalComparison.WWScalarSyntaxCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open ForwardTranslation

def ScalarSyntaxNormalizationCorrect : Prop :=
  ∀ (ι : Type) (index : ι → Nat) (s : Scalar ι),
    normalizeScalarSyntaxCode (scalarSyntaxCode index s) = scalarCode index s

def ScalarSyntaxNormalizationPrimitiveRecursive : Prop := Primrec normalizeScalarSyntaxCode

def ScalarSyntaxValueComputable : Prop :=
  Computable (fun p : Nat × List Nat => scalarSyntaxValue p.1 p.2)

def ScalarSyntaxValueSourceCorrect : Prop :=
  ∀ (ι : Type) (index : ι → Nat) (s : Scalar ι) (xs : List Nat),
    scalarSyntaxValue (scalarSyntaxCode index s) xs = s.value (fun i => xs.getD (index i) 0 + 1)
end LogicLineages.OrdinalComparison.Source.Targets
