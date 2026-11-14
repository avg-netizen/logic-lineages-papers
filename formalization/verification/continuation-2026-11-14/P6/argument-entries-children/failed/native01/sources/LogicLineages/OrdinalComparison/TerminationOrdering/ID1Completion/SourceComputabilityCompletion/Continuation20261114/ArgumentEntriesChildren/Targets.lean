module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def NativeChildrenAndDecrease : Prop :=
  (∀ (n : Nat) (c : NumberedAuxiliaryCoding.Code (Fin n)),
    evaluate children (List.Vector.ofFn ![NumberedLeastCodeRepresentative.codeNumber c]) =
      NumberedMultisetNumeric.numbersNumber
        ((NumberedSyntaxBoundsPrimrecSupportProof.children c).map NumberedLeastCodeRepresentative.codeNumber)) ∧
  (∀ (n : Nat) (c child : NumberedAuxiliaryCoding.Code (Fin n)),
    child ∈ NumberedSyntaxBoundsPrimrecSupportProof.children c →
    NumberedLeastCodeRepresentative.codeNumber child < NumberedLeastCodeRepresentative.codeNumber c)
def InternalUnary : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (ordinary : Bool) (raw metadata child listCode : OTerm alpha),
  Nonempty (Derivation body Delta (graph2
    (if ordinary then OriginalRawSyntaxTransport.ordinaryConstructor else OriginalRawSyntaxTransport.lambdaConstructor)
    raw metadata child)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode child (numeral 0))) →
  Nonempty (Derivation body Delta (graph1 children listCode raw))
def InternalBinary : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (cons : Bool) (raw tau left right rest listCode : OTerm alpha),
  Nonempty (Derivation body Delta (graph3
    (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor)
    raw tau left right)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest right (numeral 0))) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode left rest)) →
  Nonempty (Derivation body Delta (graph1 children listCode raw))
def InternalNumbered : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw k hd tau base ts extras rest listCode : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw
    ![k,hd,tau,base,ts,extras])) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest extras (numeral 0))) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode base rest)) →
  Nonempty (Derivation body Delta (graph1 children listCode raw))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.Targets
