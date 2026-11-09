module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.RawScalarDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ParameterSlice
open InternalOriginalUniformDescentSelection (Data validity representative selectedTyped)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Native pointwise equality of the THREE actual callback slices used by
the original composite Programs. This is not an internal reflection rule. -/
def Atomic (data : Data) (p q : Nat) : Prop :=
  (∀ value : Nat, evaluate data.oldRepresentative (List.Vector.ofFn ![value,p]) =
    evaluate data.oldRepresentative (List.Vector.ofFn ![value,q])) ∧
  ((∀ value : Nat, evaluate (validity data) (List.Vector.ofFn ![value,p]) =
    evaluate (validity data) (List.Vector.ofFn ![value,q])) ∧
  ∀ typ : Nat, evaluate data.member (List.Vector.ofFn ![typ,p]) =
    evaluate data.member (List.Vector.ofFn ![typ,q]))

/-- ALL raw values/types/application inputs are retained. The same Data
and every literal Program precede the two arbitrary natural parameters. -/
structure Composite (data : Data) (p q : Nat) : Prop where
  transition : ∀ value : Nat,
    evaluate (InternalParameterizedBoundedDescentNormalizer.transition data.oldRepresentative (validity data))
      (List.Vector.ofFn ![value,p]) =
    evaluate (InternalParameterizedBoundedDescentNormalizer.transition data.oldRepresentative (validity data))
      (List.Vector.ofFn ![value,q])
  representative : ∀ value : Nat,
    evaluate (representative data) (List.Vector.ofFn ![value,p]) =
      evaluate (representative data) (List.Vector.ofFn ![value,q])
  scalar : ∀ value : Nat,
    evaluate (SourceComputabilityCompletion.RawScalar.checker data) (List.Vector.ofFn ![value,p]) =
      evaluate (SourceComputabilityCompletion.RawScalar.checker data) (List.Vector.ofFn ![value,q])
  typed : ∀ value typ : Nat,
    evaluate (selectedTyped data) (List.Vector.ofFn ![value,typ,p]) =
      evaluate (selectedTyped data) (List.Vector.ofFn ![value,typ,q])
  fold : ∀ value : Nat,
    evaluate (InternalParameterizedCanonicalResultFold.foldN data) (List.Vector.ofFn ![value,p]) =
      evaluate (InternalParameterizedCanonicalResultFold.foldN data) (List.Vector.ofFn ![value,q])
  application : ∀ domain codomain function argument : Nat,
    evaluate (InternalParameterizedCanonicalResultFold.actualJ data)
      (List.Vector.ofFn ![domain,codomain,function,argument,p]) =
    evaluate (InternalParameterizedCanonicalResultFold.actualJ data)
      (List.Vector.ofFn ![domain,codomain,function,argument,q])

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ParameterSlice
