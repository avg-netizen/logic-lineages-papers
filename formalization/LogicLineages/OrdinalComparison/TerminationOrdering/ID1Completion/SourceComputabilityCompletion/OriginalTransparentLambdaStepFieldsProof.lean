module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepPrefixProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalApplicationStepPeelSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalLambdaGuardLeaf
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

abbrev childPrograms : Fin 4 → Program 4 := ![sourceBody,targetBody,childCertificate,childParameter]

/-- Pay the literal source/target lambda tests and all matching fields. -/
theorem matching (s t cert parameter childS childT d e arrow : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields s d e childS arrow)))
    (ht : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields t d e childT arrow))) :
    Nonempty (Derivation body Delta (graph4 sourceLambda (suc z) s t cert parameter)) ∧
    Nonempty (Derivation body Delta (graph4 matchingTarget (suc z) s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  have hsTest := sameAccept OriginalLambdaConstructor.tag (InternalLessThan.constantOne 1)
    (suc z) (Fin.cons s Fin.elim0) (andLeft hs) (InternalLessThanSupportProof.oneConstantValue _)
  have htTest := sameAccept OriginalLambdaConstructor.tag (InternalLessThan.constantOne 1)
    (suc z) (Fin.cons t Fin.elim0) (andLeft ht) (InternalLessThanSupportProof.oneConstantValue _)
  have hsAt := unaryValue lambdaTest (.projection 0) (suc z) s xs hsTest (projectionValue 0 xs)
  have htAt := unaryValue lambdaTest (.projection 1) (suc z) t xs htTest (projectionValue 1 xs)
  have hsType := unaryValue InternalUnpair.left (.projection 0) arrow s xs
    (andLeft (andRight hs)) (projectionValue 0 xs)
  have htType := unaryValue InternalUnpair.left (.projection 1) arrow t xs
    (andLeft (andRight ht)) (projectionValue 1 xs)
  have hsDom := unaryValue OriginalLambdaConstructor.domain (.projection 0) d s xs
    (andLeft (andRight (andRight (andRight hs)))) (projectionValue 0 xs)
  have htDom := unaryValue OriginalLambdaConstructor.domain (.projection 1) d t xs
    (andLeft (andRight (andRight (andRight ht)))) (projectionValue 1 xs)
  have htype := sameAccept (leftOf (.projection 1)) (leftOf (.projection 0)) arrow xs htType hsType
  have hdomain := sameAccept (.composition OriginalLambdaConstructor.domain (fun _ : Fin 1 => .projection 1))
    sourceDomain d xs htDom hsDom
  exact ⟨hsAt,conjunctionAccept targetLambda _ xs htAt (conjunctionAccept _ _ xs htype hdomain)⟩

/-- All four actual selectors agree with the original constructor/prefix and
parameter witnesses. No invented independent child tuple is introduced. -/
theorem selectors (s t cert parameter childS childT childCert childParam d e arrow context gamma extended : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields s d e childS arrow)))
    (ht : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields t d e childT arrow)))
    (hc : Nonempty (Derivation body Delta (graph1 stripCertificate childCert cert)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
    (he : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended d gamma)))
    (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParam context extended))) :
    ∀ i : Fin 4, Nonempty (Derivation body Delta
      (programGraph (childPrograms i) (![childS,childT,childCert,childParam] i)
        (Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))))) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  have htype := unaryValue InternalUnpair.left (.projection 0) arrow s xs
    (andLeft (andRight hs)) (projectionValue 0 xs)
  have htail := andLeft (andRight (InternalListCodecSupportProof.consDestruction arrow d e
    (andLeft (andRight (andRight hs)))))
  have hcodomain := unaryValue InternalListCodec.tailCode (leftOf (.projection 0)) e arrow xs htail htype
  have hsource := binaryValue OriginalLambdaConstructor.bodyCode sourceCodomain (.projection 0)
    childS e s xs (andRight (andRight (andRight (andRight hs)))) hcodomain (projectionValue 0 xs)
  have htarget := binaryValue OriginalLambdaConstructor.bodyCode sourceCodomain (.projection 1)
    childT e t xs (andRight (andRight (andRight (andRight ht)))) hcodomain (projectionValue 1 xs)
  have hcert := unaryValue stripCertificate (.projection 2) childCert cert xs hc (projectionValue 2 xs)
  have hcontext := unaryValue InternalUnpair.left (.projection 3) context parameter xs
    (pairLeft parameter context gamma hp) (projectionValue 3 xs)
  have hgamma := unaryValue InternalUnpair.right (.projection 3) gamma parameter xs
    (pairRight parameter context gamma hp) (projectionValue 3 xs)
  have hdomain := unaryValue OriginalLambdaConstructor.domain (.projection 0) d s xs
    (andLeft (andRight (andRight (andRight hs)))) (projectionValue 0 xs)
  have hextended := binaryValue InternalListCodec.consCode sourceDomain (rightOf (.projection 3))
    extended d gamma xs he hdomain hgamma
  have hparameter := binaryValue InternalPairing.pairing (leftOf (.projection 3))
    (consOf sourceDomain (rightOf (.projection 3))) childParam context extended xs hcp hcontext hextended
  intro i
  exact Fin.cases hsource (Fin.cases htarget (Fin.cases hcert
    (Fin.cases hparameter (fun k => Fin.elim0 k)))) i
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepFieldsProof
