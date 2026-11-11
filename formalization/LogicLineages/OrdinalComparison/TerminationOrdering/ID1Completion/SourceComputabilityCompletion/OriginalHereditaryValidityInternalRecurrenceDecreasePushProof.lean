module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreaseArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreasePushProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalOriginalOrderSyntaxProof InternalPairingSumBounds
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalPushSyntaxProof OriginalHereditaryValidityInternalStateSupportProof
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
open OriginalHereditaryValidityInternalRecurrenceDecreaseSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceDecreaseArithmeticProof

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem pushedApplicationDecrease (out fn arg parameter rest payload tail previous fp ap : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (PushedApplication out fn arg parameter rest)))
    (hf : Nonempty (Derivation body Delta (graph1 InternalUnpair.right fp fn)))
    (ha : Nonempty (Derivation body Delta (graph1 InternalUnpair.right ap arg)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (hb : Nonempty (Derivation body Delta (weakBound (childFuelSum fp ap) payload)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc payload) tail)))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply pushedApplicationCases out fn arg parameter rest _ hp
  intro beta j Theta work suffix fnFrame argFrame hj fields
  rw [decreasedRename]
  have hf' := renameInto hf j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [graph1Rename] at hf' ha'
  have ht' := renameInto ht j Theta hj
  rw [fuelRename] at ht'
  have hb' := renameInto hb j Theta hj
  simp only [weakBound,InternalLessThan.strictLess,childFuelSum,orderRename,addRelabel,sucRelabel] at hb'
  have he' := renameInto he j Theta hj
  simp only [eqnRelabel,addRelabel,sucRelabel] at he'
  have hff := frameValue fnFrame (fn.relabel j) (parameter.relabel j) (fp.relabel j)
    (andLeft (andRight (andRight fields))) hf'
  have haf := frameValue argFrame (arg.relabel j) (parameter.relabel j) (ap.relabel j)
    (andRight (andRight (andRight (andRight fields)))) ha'
  have htail := consValue suffix argFrame (rest.relabel j) (suc (ap.relabel j))
    (tail.relabel j) (andLeft (andRight (andRight (andRight fields)))) haf ht'
  have hwork := consValue work fnFrame suffix (suc (fp.relabel j))
    (add (suc (ap.relabel j)) (tail.relabel j)) (andLeft (andRight fields)) hff htail
  exact decreasedIntro (out.relabel j) (previous.relabel j) work
    (add (suc (fp.relabel j)) (add (suc (ap.relabel j)) (tail.relabel j)))
    (andLeft fields) hwork
    (applicationLess (fp.relabel j) (ap.relabel j) (payload.relabel j)
      (tail.relabel j) (previous.relabel j) hb' he')

 theorem pushedLambdaDecrease (out child parameter rest payload tail previous bp : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (PushedFrame out child parameter rest)))
    (hf : Nonempty (Derivation body Delta (graph1 InternalUnpair.right bp child)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (hb : Nonempty (Derivation body Delta (weakBound (suc bp) payload)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc payload) tail)))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply pushedFrameCases out child parameter rest _ hp
  intro beta j Theta work frame hj fields
  rw [decreasedRename]
  have hf' := renameInto hf j Theta hj
  rw [graph1Rename] at hf'
  have ht' := renameInto ht j Theta hj
  rw [fuelRename] at ht'
  have hb' := renameInto hb j Theta hj
  simp only [weakBound,InternalLessThan.strictLess,orderRename,sucRelabel] at hb'
  have he' := renameInto he j Theta hj
  simp only [eqnRelabel,addRelabel,sucRelabel] at he'
  have hframe := frameValue frame (child.relabel j) (parameter.relabel j) (bp.relabel j)
    (andRight (andRight fields)) hf'
  have hwork := consValue work frame (rest.relabel j) (suc (bp.relabel j)) (tail.relabel j)
    (andLeft (andRight fields)) hframe ht'
  exact decreasedIntro (out.relabel j) (previous.relabel j) work
    (add (suc (bp.relabel j)) (tail.relabel j)) (andLeft fields) hwork
    (childLess (suc (bp.relabel j)) (payload.relabel j) (tail.relabel j) (previous.relabel j) hb' he')

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreasePushProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreasePushProof
