module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ParameterSliceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.DecodedSourceCalibration
open Source
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformParameterLeaves (parameterObject)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Native semantics at the caller's UNCHANGED raw parameter. The one Gamma
works for all values/types/applications. No encode(decode(rawContext)) law
is used. Source validity and target validity remain distinct obligations. -/
structure DecodedCalibration (n : Nat) (arity : Fin n → Nat) (d : Data)
    (parameter : Nat) (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty) : Prop where
  objectSlice : ∀ value : Nat, parameterObject value parameter = some (Gamma,value)
  targetValidity : ∀ value : Nat,
    evaluate (InternalOriginalUniformDescentSelection.targetValidity d)
        (List.Vector.ofFn ![value,parameter]) =
      InternalOriginalStepGuard.targetValidityValue n arity Gamma value
  sourceValidity : ∀ value : Nat,
    evaluate (InternalOriginalUniformDescentSelection.validity d)
        (List.Vector.ofFn ![value,parameter]) =
      InternalOriginalStepGuard.sourceValidityValue n arity ctx.1.1 ctx.1.2 Gamma value
  representative : ∀ value : Nat,
    evaluate (InternalOriginalUniformDescentSelection.representative d)
        (List.Vector.ofFn ![value,parameter]) =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity ctx.1.1 ctx.1.2 Gamma value
  scalar : ∀ value : Nat,
    evaluate (SourceComputabilityCompletion.RawScalar.checker d)
        (List.Vector.ofFn ![value,parameter]) =
      (NumberedNumericCarrier.canonicalCarrierTest n arity ctx.1.1 ctx.1.2 Gamma value).toNat
  typed : ∀ value typ : Nat,
    evaluate (InternalOriginalUniformDescentSelection.selectedTyped d)
        (List.Vector.ofFn ![value,typ,parameter]) =
      InternalOriginalTypedCarrier.typedValue n arity ctx.1.1 ctx.1.2 Gamma
        (List.Vector.ofFn ![value,typ])
  fold : ∀ value : Nat,
    evaluate (InternalParameterizedCanonicalResultFold.foldN d)
        (List.Vector.ofFn ![value,parameter]) =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity ctx.1.1 ctx.1.2 Gamma value
  goodRun : ∀ value : Nat,
    evaluate (InternalParameterizedCanonicalResultFold.goodRunH d)
      (List.Vector.ofFn ![value,parameter]) = 1
  application : ∀ domain codomain function argument : Nat,
    evaluate (InternalParameterizedCanonicalResultFold.actualJ d)
        (List.Vector.ofFn ![domain,codomain,function,argument,parameter]) =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity ctx.1.1 ctx.1.2 Gamma
        (ApplicationCertificateLift.applicationValue (List.Vector.ofFn
          ![domain,codomain,function,
            InternalQuotientEdgeChecker.targetRepresentativeValue n arity ctx.1.1 ctx.1.2 Gamma argument]))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.DecodedSourceCalibration
