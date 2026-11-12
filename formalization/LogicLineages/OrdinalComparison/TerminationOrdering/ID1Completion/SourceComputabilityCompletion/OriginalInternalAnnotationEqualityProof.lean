module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationChildBinaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationEqualityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem pairFields (p q a b x y : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p a b)))
 (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing q x y)))
 (he : Nonempty (Derivation body Delta (eqn p q))) :
 Nonempty (Derivation body Delta (eqn a x ⊓ eqn b y)) := by
 have hl := headTransport InternalUnpair.left a p q Fin.elim0 he (pairLeft p a b hp)
 have hr := headTransport InternalUnpair.right b p q Fin.elim0 he (pairRight p a b hp)
 obtain ⟨ha⟩ := valueUnique InternalUnpair.left a x (Fin.cons q Fin.elim0) hl (pairLeft q x y hq)
 obtain ⟨hb⟩ := valueUnique InternalUnpair.right b y (Fin.cons q Fin.elim0) hr (pairRight q x y hq)
 exact ⟨Derivation.conjunctionIntroduction ha hb⟩
theorem annotationFields (index role typ raw a b roleA typeA roleB typeB : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph4 OriginalHereditaryAnnotatedExpansion.annotation a index role typ raw)))
 (hb : Nonempty (Derivation body Delta (graph4 OriginalHereditaryAnnotatedExpansion.annotation b index role typ raw)))
 (hpa : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing a roleA typeA)))
 (hpb : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing b roleB typeB))) :
 Nonempty (Derivation body Delta (eqn roleA roleB ⊓ eqn typeA typeB)) :=
 pairFields a b roleA typeA roleB typeB hpa hpb
  (valueUnique OriginalHereditaryAnnotatedExpansion.annotation a b
   (Fin.cons index (Fin.cons role (Fin.cons typ (Fin.cons raw Fin.elim0)))) ha hb)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationEqualityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationEqualityProof
