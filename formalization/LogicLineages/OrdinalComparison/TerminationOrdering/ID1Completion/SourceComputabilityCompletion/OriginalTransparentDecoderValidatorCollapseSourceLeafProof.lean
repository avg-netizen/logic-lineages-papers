module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrencePopProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaNodeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalApplicationCertificateConstructorsSupportProof
open InternalTagArithmeticSyntaxProof (z)
open OriginalLambdaConstructorGraphSyntaxProof (oneRename)
open OriginalTypedDecoderTransportLogicalProof (notRename)
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalHereditaryValidityInternalNodeSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceAcceptanceProof (acceptanceFactors)
open OriginalHereditaryValidityInternalRecurrencePopProof (popRecurrence)
open OriginalTransparentLambdaValidity OriginalTransparentLambdaValidityInternal
open OriginalTransparentLambdaValidityInternalBranchSupportProof
open OriginalTransparentLambdaValidityInternalBranchValueProof
open OriginalTransparentLambdaValidityInternalSourceCheckProof (sourceCheck)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem tagNotEqual (raw tag : OTerm alpha) (k : Nat)
    (ht : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag tag raw)))
    (hn : Nonempty (Derivation body Gamma (TagIs k raw).not)) :
    Nonempty (Derivation body Gamma (equal tag (numeral k)).not) := by
  let E := equal tag (numeral k)
  have he : Nonempty (Derivation body (E :: Gamma) (InternalTagArithmeticSyntaxProof.eqn tag (numeral k))) := by
    simpa only [E,equalEqn] using
      (show Nonempty (Derivation body (E :: Gamma) E) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hv⟩ := outputTransport OriginalLambdaConstructor.tag tag (numeral k)
    (Fin.cons raw Fin.elim0) he (addAssumption ht E)
  obtain ⟨hn⟩ := addAssumption hn E
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn hv)⟩

/-- On an opaque branch the actual application-only membership implication
is vacuous; no membership acceptance or semantic typing is assumed. -/
theorem nodeOffApplication (s t m : Program 2) (raw parameter : OTerm alpha)
    (h2 : Nonempty (Derivation body Gamma (TagIs 2 raw).not))
    (hs : Nonempty (Derivation body Gamma (graph2 s (numeral 1) raw parameter)))
    (ht : Nonempty (Derivation body Gamma (graph2 t (numeral 1) raw parameter))) :
    Nonempty (Derivation body Gamma (NodeFactors s t m raw parameter)) := by
  let qs : Fin 2 → Program 1 := ![InternalUnpair.left,OriginalLambdaConstructor.tag]
  apply queryCases qs (Fin.cons raw Fin.elim0) _
  intro beta j ys Delta hj hq
  simp only [consTermRename,emptyRename] at hq
  simp only [factorsRename]
  have h2' := renameInto h2 j Delta hj
  simp only [TagIs,notRename,graph1Rename,numeralRename] at h2'
  have hs' := renameInto hs j Delta hj
  have ht' := renameInto ht j Delta hj
  simp only [graph2Rename,oneRename] at hs' ht'
  have hn := tagNotEqual (raw.relabel j) (ys 1) 2 (hq 1) h2'
  let E := equal (ys 1) (numeral 2)
  obtain ⟨hn⟩ := addAssumption hn E
  have hm : Nonempty (Derivation body Delta
      (E.imp (graph2 m (numeral 1) (ys 0) (parameter.relabel j)))) :=
    ⟨Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination hn (Derivation.hypothesis List.mem_cons_self)))⟩
  exact andIntro hs' (andIntro ht'
    (fieldsIntro m (raw.relabel j) (parameter.relabel j) (ys 0) (ys 1)
      (andIntro (hq 0) (andIntro (hq 1) hm))))

theorem popAcceptanceEquation (s t m : Program 2) (raw parameter : OTerm alpha)
    (h2 : Nonempty (Derivation body Gamma (TagIs 2 raw).not))
    (h1 : Nonempty (Derivation body Gamma (TagIs 1 raw).not)) :
    Nonempty (Derivation body Gamma
      ((graph2 (validator s t m) (numeral 1) raw parameter).iff
        (graph2 s (numeral 1) raw parameter ⊓ graph2 t (numeral 1) raw parameter))) := by
  let A := graph2 (validator s t m) (numeral 1) raw parameter
  let B := graph2 s (numeral 1) raw parameter ⊓ graph2 t (numeral 1) raw parameter
  have hf : Nonempty (Derivation body (A :: Gamma) B) := by
    have hn := acceptanceFactors s t m raw parameter
      (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact andIntro (andLeft hn) (andLeft (andRight hn))
  have hb : Nonempty (Derivation body (B :: Gamma) A) := by
    have h : Nonempty (Derivation body (B :: Gamma) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hn := nodeOffApplication s t m raw parameter (addAssumption h2 B) (andLeft h) (andRight h)
    apply programCases OriginalLambdaConstructor.tag (Fin.cons raw Fin.elim0) _
    intro beta j Delta tag hj htag
    simp only [A,graph2Rename,oneRename]
    simp only [consTermRename,emptyRename] at htag
    have hn' := renameInto hn j Delta hj
    rw [factorsRename] at hn'
    have h2' := renameInto (addAssumption h2 B) j Delta hj
    have h1' := renameInto (addAssumption h1 B) j Delta hj
    simp only [TagIs,notRename,graph1Rename,numeralRename] at h2' h1'
    exact popRecurrence s t m (raw.relabel j) (parameter.relabel j) tag hn' htag
      (tagNotEqual (raw.relabel j) tag 2 htag h2')
      (tagNotEqual (raw.relabel j) tag 1 htag h1')
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

/-- The unchanged bounded machine on every nonapplication/nonlambda raw
input accepts exactly its two original opaque callbacks. -/
theorem opaqueAcceptance (data : Data) (raw parameter : OTerm alpha)
    (h2 : Nonempty (Derivation body Gamma (TagIs 2 raw).not))
    (h1 : Nonempty (Derivation body Gamma (TagIs 1 raw).not)) :
    Nonempty (Derivation body Gamma
      ((graph2 (validator (sourceRoot data) (targetRoot data) data.member)
          (numeral 1) raw parameter).iff
        (graph2 data.oldSource (numeral 1) raw parameter ⊓
          graph2 data.oldTarget (numeral 1) raw parameter))) := by
  let A := graph2 (validator (sourceRoot data) (targetRoot data) data.member) (numeral 1) raw parameter
  let B := graph2 data.oldSource (numeral 1) raw parameter ⊓ graph2 data.oldTarget (numeral 1) raw parameter
  have hf : Nonempty (Derivation body (A :: Gamma) B) := by
    have hn := acceptanceFactors (sourceRoot data) (targetRoot data) data.member raw parameter
      (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact andIntro
      (dispatchOpaque data.oldSource (sourceCheck data) (numeral 1) raw parameter
        (addAssumption h2 A) (addAssumption h1 A) (andLeft hn))
      (dispatchOpaque data.oldTarget lambdaShape (numeral 1) raw parameter
        (addAssumption h2 A) (addAssumption h1 A) (andLeft (andRight hn)))
  have hb : Nonempty (Derivation body (B :: Gamma) A) := by
    have h : Nonempty (Derivation body (B :: Gamma) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hs := dispatchOpaqueValue data.oldSource (sourceCheck data) (numeral 1) raw parameter
      (addAssumption h2 B) (addAssumption h1 B) (andLeft h)
    have ht := dispatchOpaqueValue data.oldTarget lambdaShape (numeral 1) raw parameter
      (addAssumption h2 B) (addAssumption h1 B) (andRight h)
    have hn := nodeOffApplication (sourceRoot data) (targetRoot data) data.member raw parameter
      (addAssumption h2 B) hs ht
    apply programCases OriginalLambdaConstructor.tag (Fin.cons raw Fin.elim0) _
    intro beta j Delta tag hj htag
    simp only [A,graph2Rename,oneRename]
    simp only [consTermRename,emptyRename] at htag
    have hn' := renameInto hn j Delta hj
    rw [factorsRename] at hn'
    have h2' := renameInto (addAssumption h2 B) j Delta hj
    have h1' := renameInto (addAssumption h1 B) j Delta hj
    simp only [TagIs,notRename,graph1Rename,numeralRename] at h2' h1'
    exact popRecurrence (sourceRoot data) (targetRoot data) data.member
      (raw.relabel j) (parameter.relabel j) tag hn' htag
      (tagNotEqual (raw.relabel j) tag 2 htag h2')
      (tagNotEqual (raw.relabel j) tag 1 htag h1')
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLeafProof
