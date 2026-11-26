module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreasePushProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalOriginalOrderSyntaxProof InternalPairingSumBounds
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalPushSyntaxProof
open OriginalTypedDecoderInternalFuelSupportProof
open OriginalTypedDecoderInternalFuelDecreaseSyntaxProof
open OriginalTypedDecoderInternalFuelDecreaseArithmeticProof

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem pushedOneDecrease (out mode gamma typ child rest raw tail previous : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPushOne out mode gamma typ child rest)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (hb : Nonempty (Derivation body Delta (weakBound (suc child) raw)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc raw) tail)))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply stepPushOneCases out mode gamma typ child rest _ hp
  intro beta j Theta ys hj fields
  rw [decreasedRename]
  have ht' := renameInto ht j Theta hj
  rw [fuelRename] at ht'
  have hb' := renameInto hb j Theta hj
  simp only [weakBound,InternalLessThan.strictLess,orderRename,sucRelabel] at hb'
  have he' := renameInto he j Theta hj
  simp only [eqnRelabel,addRelabel,sucRelabel] at he'
  have hr := requestValue (ys 0) (mode.relabel j) (gamma.relabel j)
    (typ.relabel j) (child.relabel j) (andLeft fields)
  have hw := consValue (ys 1) (ys 0) (rest.relabel j) (suc (child.relabel j))
    (tail.relabel j) (andLeft (andRight fields)) hr ht'
  exact decreasedIntro (out.relabel j) (previous.relabel j) (ys 1)
    (add (suc (child.relabel j)) (tail.relabel j)) (andRight (andRight fields)) hw
    (childLess (suc (child.relabel j)) (raw.relabel j) (tail.relabel j)
      (previous.relabel j) hb' he')

 theorem pushedTwoDecrease
    (out mode₁ gamma₁ typ₁ first mode₂ gamma₂ typ₂ second rest raw tail previous : OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (StepPushTwo out mode₁ gamma₁ typ₁ first mode₂ gamma₂ typ₂ second rest)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (hb : Nonempty (Derivation body Delta (weakBound (childFuelSum first second) raw)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc raw) tail)))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply stepPushTwoCases out mode₁ gamma₁ typ₁ first mode₂ gamma₂ typ₂ second rest _ hp
  intro beta j Theta ys hj fields
  rw [decreasedRename]
  have ht' := renameInto ht j Theta hj
  rw [fuelRename] at ht'
  have hb' := renameInto hb j Theta hj
  simp only [weakBound,InternalLessThan.strictLess,childFuelSum,orderRename,addRelabel,sucRelabel] at hb'
  have he' := renameInto he j Theta hj
  simp only [eqnRelabel,addRelabel,sucRelabel] at he'
  have hfirst := requestValue (ys 0) (mode₁.relabel j) (gamma₁.relabel j)
    (typ₁.relabel j) (first.relabel j) (andLeft fields)
  have hsecond := requestValue (ys 1) (mode₂.relabel j) (gamma₂.relabel j)
    (typ₂.relabel j) (second.relabel j) (andLeft (andRight fields))
  have hsuffix := consValue (ys 2) (ys 1) (rest.relabel j) (suc (second.relabel j))
    (tail.relabel j) (andLeft (andRight (andRight fields))) hsecond ht'
  have hw := consValue (ys 3) (ys 0) (ys 2) (suc (first.relabel j))
    (add (suc (second.relabel j)) (tail.relabel j))
    (andLeft (andRight (andRight (andRight fields)))) hfirst hsuffix
  exact decreasedIntro (out.relabel j) (previous.relabel j) (ys 3)
    (add (suc (first.relabel j)) (add (suc (second.relabel j)) (tail.relabel j)))
    (andRight (andRight (andRight (andRight fields)))) hw
    (applicationLess (first.relabel j) (second.relabel j) (raw.relabel j)
      (tail.relabel j) (previous.relabel j) hb' he')

 theorem poppedDecrease (out rest raw tail previous : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StepLive out rest)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc raw) tail)))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) :=
  decreasedIntro out previous rest tail hs ht (tailLess raw tail previous he)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreasePushProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreasePushProof
