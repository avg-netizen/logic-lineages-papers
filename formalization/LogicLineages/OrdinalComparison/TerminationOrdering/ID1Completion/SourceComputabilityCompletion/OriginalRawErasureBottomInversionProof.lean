module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawErasureBottomInversionConstructorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldOffDomainLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawErasureBottomInversionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open OriginalRawSyntaxTransportInternalParserUnaryProof OriginalRawSyntaxTransportInternalParserBinaryProof OriginalRawSyntaxTransportInternalParserNumberedProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNeApply)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalRawErasureBottomInversionConstructorProof

def TagPreservation (n : Nat) : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (raw out d k : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 rawTag (numeral n) raw)) →
 Nonempty (Derivation body Delta (graph3 eraseRaw out d k raw)) →
 Nonempty (Derivation body Delta (graph1 rawTag (numeral n) out))

theorem lambdaTagPreservation : TagPreservation 1 := by
 intro body alpha Delta raw out d k ht ho
 apply lambdaCases raw _ ht
 intro beta j Theta domain child hj hc
 simp only [graph1Rename,numeralRename]
 have ho' := renameInto ho j Theta hj
 rw [graph3Rename] at ho'
 exact lambdaPreserved (raw.relabel j) (out.relabel j) (d.relabel j) (k.relabel j) domain child hc ho'

theorem ordinaryTagPreservation : TagPreservation 4 := by
 intro body alpha Delta raw out d k ht ho
 apply ordinaryCases raw _ ht
 intro beta j Theta head child hj hc
 simp only [graph1Rename,numeralRename]
 have ho' := renameInto ho j Theta hj
 rw [graph3Rename] at ho'
 exact ordinaryPreserved (raw.relabel j) (out.relabel j) (d.relabel j) (k.relabel j) head child hc ho'

theorem applicationTagPreservation : TagPreservation 2 := by
 intro body alpha Delta raw out d k ht ho
 apply applicationCases raw _ ht
 intro beta j Theta domain first second hj hc
 simp only [graph1Rename,numeralRename]
 have ho' := renameInto ho j Theta hj
 rw [graph3Rename] at ho'
 exact applicationPreserved (raw.relabel j) (out.relabel j) (d.relabel j) (k.relabel j) domain first second hc ho'

theorem consTagPreservation : TagPreservation 7 := by
 intro body alpha Delta raw out d k ht ho
 apply consCases raw _ ht
 intro beta j Theta tau first second hj hc
 simp only [graph1Rename,numeralRename]
 have ho' := renameInto ho j Theta hj
 rw [graph3Rename] at ho'
 exact consPreserved (raw.relabel j) (out.relabel j) (d.relabel j) (k.relabel j) tau first second hc ho'

theorem numberedTagPreservation : TagPreservation 5 := by
 intro body alpha Delta raw out d k ht ho
 apply numberedCases raw _ ht
 intro beta j Theta label head tau base types extras hj hc
 simp only [graph1Rename,numeralRename]
 have ho' := renameInto ho j Theta hj
 rw [graph3Rename] at ho'
 exact numberedPreserved (raw.relabel j) (out.relabel j) (d.relabel j) (k.relabel j) label head tau base types extras hc ho'

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem excludeTag (n : Nat) (hne : n ≠ 3) (preserved : TagPreservation n)
 (raw out d k tag : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 rawTag tag raw)))
 (he : Nonempty (Derivation body Delta (graph3 eraseRaw out d k raw)))
 (hb : Nonempty (Derivation body Delta (graph1 rawTag (numeral 3) out))) :
 Nonempty (Derivation body Delta (equal tag (numeral n)).not) := by
 let H := equal tag (numeral n)
 have hh : Nonempty (Derivation body (H :: Delta) (eqn tag (numeral n))) := by
   simpa only [H,equalEqn] using (show Nonempty (Derivation body (H :: Delta) H) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
 have htn := outputTransport rawTag tag (numeral n) (Fin.cons raw Fin.elim0) hh (withHyp ht H)
 have hon := preserved body alpha (H :: Delta) raw out d k htn (withHyp he H)
 obtain ⟨heq⟩ := valueUnique rawTag (numeral n) (numeral 3) (Fin.cons out Fin.elim0) hon (withHyp hb H)
 exact ⟨Derivation.implicationIntroduction (numeralNeApply n 3 hne heq)⟩

theorem bottomInversion (raw out erasedType cutoff tag : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 rawTag tag raw)))
 (hn : Nonempty (Derivation body Delta (equal tag (numeral 0)).not))
 (he : Nonempty (Derivation body Delta (graph3 eraseRaw out erasedType cutoff raw)))
 (hb : Nonempty (Derivation body Delta (graph1 rawTag (numeral 3) out))) :
 Nonempty (Derivation body Delta (equal out raw)) := by
 have h1 := excludeTag 1 (by decide) lambdaTagPreservation raw out erasedType cutoff tag ht he hb
 have h4 := excludeTag 4 (by decide) ordinaryTagPreservation raw out erasedType cutoff tag ht he hb
 have h2 := excludeTag 2 (by decide) applicationTagPreservation raw out erasedType cutoff tag ht he hb
 have h5 := excludeTag 5 (by decide) numberedTagPreservation raw out erasedType cutoff tag ht he hb
 have h7 := excludeTag 7 (by decide) consTagPreservation raw out erasedType cutoff tag ht he hb
 have ha := OriginalRawSyntaxTransportInternalFoldOffDomainLeafProof.nonStructuralArity raw tag ht
   (andIntro h1 (andIntro h4 (andIntro h2 (andIntro h5 h7))))
 simpa only [equalEqn] using OriginalTwoDeletionInternalLeafProof.nonzeroRetained raw out erasedType cutoff tag ht hn ha he

theorem actualBottomInversion : OriginalRawErasureBottomInversionTargets.ActualBottomInversion := by
 intro body alpha Delta raw out erasedType cutoff tag ht hn he hb
 exact bottomInversion raw out erasedType cutoff tag ht hn he hb
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawErasureBottomInversionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawErasureBottomInversionProof
