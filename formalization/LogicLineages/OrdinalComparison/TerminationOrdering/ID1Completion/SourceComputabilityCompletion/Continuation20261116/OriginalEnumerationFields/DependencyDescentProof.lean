module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.DependencySupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesDependencyDescent.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.DependencyDescentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open InternalOriginalPairingOrderArithmeticProof (strictTransport)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalConstructorBoundsProof
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem zeroCase (key param deps child childRank code bound : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) z code)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank code)) := by
  have hraw := LayerInternalProof.rankAt key code bound param hk
  have har := SelectorTransferProof.arityAt (keyRaw (.projection 0)) ![key,param] code z hraw ha
  have hz := DependencySupportProof.zeroList key param har
  have he := valueUnique dependency deps z ![key,param] hd hz
  have h0 := headTransport contains (numeral 1) deps z (Fin.cons child Fin.elim0) he hm
  obtain ⟨hb⟩ := valueUnique contains (numeral 1) z ![z,child] h0 (containsNil child)
  exact ⟨Derivation.explosion (sucNeZeroApply hb)⟩

theorem unaryAt (key code bound param deps child childRank first firstKeyValue listCode : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 1) code)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hr : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first code)))
    (hfk : Nonempty (Derivation body Delta (graph2 firstKey firstKeyValue key param)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode firstKeyValue z))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank code)) := by
  have hraw := LayerInternalProof.rankAt key code bound param hk
  have har := SelectorTransferProof.arityAt (keyRaw (.projection 0)) ![key,param] code (numeral 1) hraw ha
  have hg := DependencySupportProof.unaryList key param firstKeyValue listCode har hfk hc
  have he := valueUnique dependency deps listCode ![key,param] hd hg
  have hl := headTransport contains (numeral 1) deps listCode (Fin.cons child Fin.elim0) he hm
  have hcf := PrimaryCarrierBound.RunProof.singletonMember listCode firstKeyValue child hc hl
  have hrt := headTransport rank childRank child firstKeyValue (Fin.cons param Fin.elim0) hcf hr
  have hfirst := DependencySupportProof.firstRank key code bound param firstKeyValue first hk hfk hf
  have heq := valueUnique rank childRank first ![firstKeyValue,param] hrt hfirst
  exact strictTransport childRank code first code heq ⟨refl code⟩ (unaryChildStrict code first ha hf)

theorem binaryAt (key code bound param deps child childRank first second firstKeyValue secondKeyValue rest listCode : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) code)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hrank : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first code)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second code)))
    (hfk : Nonempty (Derivation body Delta (graph2 firstKey firstKeyValue key param)))
    (hsk : Nonempty (Derivation body Delta (graph2 secondKey secondKeyValue key param)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest secondKeyValue z)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode firstKeyValue rest))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank code)) := by
  have hraw := LayerInternalProof.rankAt key code bound param hk
  have har := SelectorTransferProof.arityAt (keyRaw (.projection 0)) ![key,param] code (numeral 2) hraw ha
  have hg := DependencySupportProof.binaryList key param firstKeyValue secondKeyValue rest listCode har hfk hsk hr hc
  have he := valueUnique dependency deps listCode ![key,param] hd hg
  have hl := headTransport contains (numeral 1) deps listCode (Fin.cons child Fin.elim0) he hm
  have hb := binaryChildrenStrict code first second ha hf hs
  let A := equal firstKeyValue child
  apply InternalApplicationValidityStackAppendInductionCoreProof.formulaCases A
  · have h : Nonempty (Derivation body (A :: Delta) (equal firstKeyValue child)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    rw [equalEqn] at h
    obtain ⟨e⟩ := h
    have hrt := headTransport rank childRank child firstKeyValue (Fin.cons param Fin.elim0) ⟨symm e⟩
      (InternalApplicationValidityStackAppendInductionCoreProof.withHyp hrank A)
    have hfirst := InternalApplicationValidityStackAppendInductionCoreProof.withHyp
      (DependencySupportProof.firstRank key code bound param firstKeyValue first hk hfk hf) A
    have heq := valueUnique rank childRank first ![firstKeyValue,param] hrt hfirst
    exact strictTransport childRank code first code heq ⟨refl code⟩
      (InternalApplicationStepPeelSupportProof.andLeft
        (InternalApplicationValidityStackAppendInductionCoreProof.withHyp hb A))
  · have ht := PrimaryMembership.Proof.missRecover listCode firstKeyValue rest child (numeral 1)
      (InternalApplicationValidityStackAppendInductionCoreProof.withHyp hc A.not)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
      (InternalApplicationValidityStackAppendInductionCoreProof.withHyp hl A.not)
    have hcs := PrimaryCarrierBound.RunProof.singletonMember rest secondKeyValue child
      (InternalApplicationValidityStackAppendInductionCoreProof.withHyp hr A.not) ht
    have hrt := headTransport rank childRank child secondKeyValue (Fin.cons param Fin.elim0) hcs
      (InternalApplicationValidityStackAppendInductionCoreProof.withHyp hrank A.not)
    have hsecond := InternalApplicationValidityStackAppendInductionCoreProof.withHyp
      (DependencySupportProof.secondRank key code bound param secondKeyValue second hk hsk hs) A.not
    have heq := valueUnique rank childRank second ![secondKeyValue,param] hrt hsecond
    exact strictTransport childRank code second code heq ⟨refl code⟩
      (InternalApplicationStepPeelSupportProof.andRight
        (InternalApplicationValidityStackAppendInductionCoreProof.withHyp hb A.not))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.DependencyDescentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.DependencyDescentProof
