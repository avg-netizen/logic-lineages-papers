module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Literal numeric row-major cross and its exact ORIGINAL decoded-node
correspondence. Off-domain default[] is intentionally NOT asserted. -/
def NativeCorrespondence : Prop :=
  (∀ (left right : List Nat), evaluate cross (List.Vector.ofFn
      ![NumberedMultisetNumeric.numbersNumber left,NumberedMultisetNumeric.numbersNumber right]) =
    NumberedMultisetNumeric.numbersNumber (left.flatMap (fun a => right.map (fun b => Nat.pair a b)))) ∧
  (∀ (n : Nat) (source target : NumberedAuxiliaryCoding.Code (Fin n)),
    evaluate rawDependencies (List.Vector.ofFn
      ![NumberedLeastCodeRepresentative.codeNumber source,NumberedLeastCodeRepresentative.codeNumber target]) =
    NumberedMultisetNumeric.numbersNumber
      ((NumberedExchangeCodeFieldsProof.dependencies (source,target)).map (fun child =>
        Nat.pair (NumberedLeastCodeRepresentative.codeNumber child.1) (NumberedLeastCodeRepresentative.codeNumber child.2))))

/-- Every ACTUAL numeric cross member projects to members of both input lists;
no semantic/native list or hidden positional-validity witness is assumed. -/
def InternalProjection : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (left right out node sourceChild targetChild : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 cross out left right)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out node)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node sourceChild targetChild)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) left sourceChild ⊓
    graph2 contains (numeral 1) right targetChild))

/-- Both strict raw-code decreases for the explicit unguarded helper; these
facts do not install or identify the decoded/default[] original supplier. -/
def InternalDescent : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (source target out node sourceChild targetChild : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 rawDependencies out source target)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out node)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node sourceChild targetChild)) →
  Nonempty (Derivation body Delta (InternalLessThan.strictLess sourceChild source ⊓
    InternalLessThan.strictLess targetChild target))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.Targets
