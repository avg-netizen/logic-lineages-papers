module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildPacketDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportUnaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalConstructorSupportProof
open OriginalInternalJobAdmissible OriginalInternalJobAdmissibleTransportSyntaxProof
open OriginalInternalJobChildPacket
open OriginalTypedDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem packetRename {beta : Type} (H : Program 1) (M W : Program 2)
 (index role typ raw cell parameter c gamma outRole outType outRaw outGamma outParam annotation : OTerm alpha)
 (j : alpha → beta) :
 (Packet H M W index role typ raw cell parameter c gamma outRole outType outRaw outGamma outParam annotation).relabel j =
 Packet H M W (index.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j) (cell.relabel j)
 (parameter.relabel j) (c.relabel j) (gamma.relabel j) (outRole.relabel j) (outType.relabel j)
 (outRaw.relabel j) (outGamma.relabel j) (outParam.relabel j) (annotation.relabel j) := by
 simp only [Packet,conjunctionRename,graph2Rename,graph4Rename,admissibleRename]
theorem termAtTag (H : Program 1) (M W : Program 2) (tag : Nat) (h6 : tag ≠ 6) (h7 : tag ≠ 7)
 (role typ raw gamma c : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral tag) raw))) :
 Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c)) := by
 apply programCases InternalUnpair.right (Fin.cons raw Fin.elim0) _
 intro beta j Theta payload hj hp
 have ht' := renameInto ht j Theta hj
 have ha' := renameInto ha j Theta hj
 simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at ht'
 simp only [admissibleRename] at ha'
 have hp' : Nonempty (Derivation body Theta (graph1 InternalUnpair.right payload (raw.relabel j))) := hp
 have pair := reconstructPair (raw.relabel j) (numeral tag) payload ht' hp'
 have hm := OriginalInternalJobAdmissibleModeProof.termMode H M W (role.relabel j) (typ.relabel j) (raw.relabel j)
  (gamma.relabel j) (c.relabel j) (numeral tag) payload ha' pair (numeralNe tag 6 h6) (numeralNe tag 7 h7)
 simpa only [OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] using andRight hm

theorem firstCell (raw cell parameter child childParameter : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob cell raw parameter)))
 (hf : Nonempty (Derivation body Delta (graph2 (firstOf (.projection 0)) child raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstParameter childParameter raw parameter))) :
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing cell child childParameter)) :=
 binaryRecover InternalPairing.pairing (firstOf (.projection 0)) OriginalHereditaryExpansion.firstParameter
 cell child childParameter (Fin.cons raw (Fin.cons parameter Fin.elim0)) hj hf hp

theorem secondCell (raw cell parameter child : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob cell raw parameter)))
 (hf : Nonempty (Derivation body Delta (graph2 (secondOf (.projection 0)) child raw parameter))) :
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing cell child parameter)) :=
 binaryRecover InternalPairing.pairing (secondOf (.projection 0)) (.projection 1)
 cell child parameter (Fin.cons raw (Fin.cons parameter Fin.elim0)) hj hf (projectionValue 1 _)

/-- Only the annotation pair is queried; the callback never assumes its desired Program output. -/
theorem annotationCases (outRole outType : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (annotation : OTerm beta),
 (∀ p ∈ Delta, p.relabel j ∈ Theta) →
 Nonempty (Derivation body Theta (graph2 InternalPairing.pairing annotation (outRole.relabel j) (outType.relabel j))) →
 Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 apply programCases InternalPairing.pairing (Fin.cons outRole (Fin.cons outType Fin.elim0)) psi
 intro beta j Theta annotation hj hp
 exact next beta j Theta annotation hj hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildSupportProof
