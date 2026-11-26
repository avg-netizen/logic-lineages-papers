module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalIterationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorFixedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z eqn)
open OriginalTypedArgumentObservations OriginalTypedArgumentObservationsInternalIterationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem pairCoordinates (out raw acc remaining result : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out raw acc)))
 (hb : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out remaining result))) :
 Nonempty (Derivation body Delta (eqn raw remaining)) ∧
 Nonempty (Derivation body Delta (eqn acc result)) := by
 constructor
 · exact valueUnique InternalUnpair.left raw remaining (Fin.cons out Fin.elim0)
     (pairLeft out raw acc ha) (pairLeft out remaining result hb)
 · exact valueUnique InternalUnpair.right acc result (Fin.cons out Fin.elim0)
     (pairRight out raw acc ha) (pairRight out remaining result hb)

/-- Fixed runs preserve the actual accumulator suffix, including malformed
non-cons spines. Both output decompositions are identified by graph uniqueness. -/
theorem fixedSuffix (R : Program 2)
 (count raw acc1 acc2 suffix initial1 initial2 parameter out1 out2 remaining1 remaining2 result1 result2 : OTerm alpha)
 (hp1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial1 raw acc1)))
 (hp2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial2 raw acc2)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append acc2 acc1 suffix)))
 (hfixed1 : Nonempty (Derivation body Delta (graph3 (walk R) initial1 count initial1 parameter)))
 (hfixed2 : Nonempty (Derivation body Delta (graph3 (walk R) initial2 count initial2 parameter)))
 (hr1 : Nonempty (Derivation body Delta (graph3 (walk R) out1 count initial1 parameter)))
 (hr2 : Nonempty (Derivation body Delta (graph3 (walk R) out2 count initial2 parameter)))
 (hout1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out1 remaining1 result1)))
 (hout2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out2 remaining2 result2))) :
 Nonempty (Derivation body Delta (equal remaining1 remaining2 ⊓
   graph2 InternalApplicationValidityStackAppend.append result2 result1 suffix)) := by
 have he1 := valueUnique (walk R) initial1 out1 (Fin.cons count (Fin.cons initial1 (Fin.cons parameter Fin.elim0))) hfixed1 hr1
 have he2 := valueUnique (walk R) initial2 out2 (Fin.cons count (Fin.cons initial2 (Fin.cons parameter Fin.elim0))) hfixed2 hr2
 have hp1' := outputTransport InternalPairing.pairing initial1 out1 (Fin.cons raw (Fin.cons acc1 Fin.elim0)) he1 hp1
 have hp2' := outputTransport InternalPairing.pairing initial2 out2 (Fin.cons raw (Fin.cons acc2 Fin.elim0)) he2 hp2
 obtain ⟨⟨heRaw1⟩, heAcc1⟩ := pairCoordinates out1 raw acc1 remaining1 result1 hp1' hout1
 obtain ⟨⟨heRaw2⟩, heAcc2⟩ := pairCoordinates out2 raw acc2 remaining2 result2 hp2' hout2
 have heRaw : Nonempty (Derivation body Delta (equal remaining1 remaining2)) := by
   simpa only [equalEqn] using (Nonempty.intro
     (InternalTagArithmeticSupportProof.trans (InternalTagArithmeticSupportProof.symm heRaw1) heRaw2))
 have ht := headTransport InternalApplicationValidityStackAppend.append acc2 acc1 result1
   (Fin.cons suffix Fin.elim0) heAcc1 ha
 have ho := outputTransport InternalApplicationValidityStackAppend.append acc2 result2
   (Fin.cons result1 (Fin.cons suffix Fin.elim0)) heAcc2 ht
 obtain ⟨heRaw⟩ := heRaw
 obtain ⟨ho⟩ := ho
 exact ⟨Derivation.conjunctionIntroduction heRaw ho⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorFixedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorFixedProof
