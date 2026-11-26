module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBranchValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSourceCheckProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationNodeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalBetaTotalityProof
open InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationCertificateConstructorsSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalHereditaryValidityInternalNodeSyntaxProof OriginalHereditaryValidityInternalNodeSupportProof
open OriginalHereditaryValidityInternalNodeProof
open OriginalHereditaryValidityInternalRecurrenceRootFrameProof
open OriginalHereditaryValidityInternalStateSupportProof
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalTransparentLambdaValidityInternalBranchValueProof
open OriginalTransparentLambdaValidityInternalSourceCheckProof (sourceCheck)
open OriginalTransparentLambdaValidity OriginalTransparentLambdaValidityInternal
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem applicationMemberRecover (s t m : Program 2) (raw parameter typ : OTerm alpha)
    (htyp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ raw)))
    (htag : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag (numeral 2) raw)))
    (hn : Nonempty (Derivation body Gamma (NodeFactors s t m raw parameter))) :
    Nonempty (Derivation body Gamma (graph2 m (numeral 1) typ parameter)) := by
  apply rootFrameCases raw parameter _
  intro beta j Delta state work frame payload hj hi hframe hpay
  have hf := renameInto hn j Delta hj
  have ht := renameInto htyp j Delta hj
  have hg := renameInto htag j Delta hj
  simp only [factorsRename] at hf
  simp only [graph1Rename,numeral,sucRelabel,zRelabel] at ht hg
  simp only [graph2Rename,numeral,sucRelabel,zRelabel]
  have hs := initialSelectors state (raw.relabel j) (parameter.relabel j) hi
  have hc := acceptFactors s t m state (raw.relabel j) (parameter.relabel j) (andLeft hs) (andRight hs) hf
  obtain ⟨himp⟩ := andRight (andRight (recoverFields s t m state (raw.relabel j)
    (parameter.relabel j) (typ.relabel j) (numeral 2) (andLeft hs) (andRight hs) ht hg hc))
  exact ⟨Derivation.implicationElimination himp (by
    simpa only [equalEqn] using (InternalTagArithmeticSupportProof.refl (numeral 2)))⟩

theorem applicationNodeValue (s t m : Program 2) (raw parameter typ : OTerm alpha)
    (htyp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ raw)))
    (htag : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag (numeral 2) raw)))
    (hs : Nonempty (Derivation body Gamma (graph2 s (numeral 1) raw parameter)))
    (ht : Nonempty (Derivation body Gamma (graph2 t (numeral 1) raw parameter)))
    (hm : Nonempty (Derivation body Gamma (graph2 m (numeral 1) typ parameter))) :
    Nonempty (Derivation body Gamma (NodeFactors s t m raw parameter)) := by
  obtain ⟨hm⟩ := hm
  exact andIntro hs (andIntro ht (fieldsIntro m raw parameter typ (numeral 2)
    (andIntro htyp (andIntro htag
      ⟨Derivation.implicationIntroduction (addHyp hm _)⟩))))

theorem applicationNodeEquation (s t m : Program 2) (raw parameter typ : OTerm alpha)
    (htyp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ raw)))
    (htag : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag (numeral 2) raw)))
    (hs : Nonempty (Derivation body Gamma (graph2 s (numeral 1) raw parameter)))
    (ht : Nonempty (Derivation body Gamma (graph2 t (numeral 1) raw parameter))) :
    Nonempty (Derivation body Gamma
      ((NodeFactors s t m raw parameter).iff (graph2 m (numeral 1) typ parameter))) := by
  let A := NodeFactors s t m raw parameter
  let B := graph2 m (numeral 1) typ parameter
  obtain ⟨hf⟩ := applicationMemberRecover s t m raw parameter typ (addAssumption htyp A)
    (addAssumption htag A) (show Nonempty (Derivation body (A :: Gamma) A) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := applicationNodeValue s t m raw parameter typ (addAssumption htyp B)
    (addAssumption htag B) (addAssumption hs B) (addAssumption ht B)
    (show Nonempty (Derivation body (B :: Gamma) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem sourceApplicationNode (data : InternalOriginalUniformDescentSelection.Data)
    (raw parameter typ : OTerm alpha)
    (htyp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ raw)))
    (htag : Nonempty (Derivation body Gamma (TagIs 2 raw))) :
    Nonempty (Derivation body Gamma
      ((NodeFactors (sourceRoot data) (targetRoot data) data.member raw parameter).iff
        (graph2 data.member (numeral 1) typ parameter))) := by
  have he : Nonempty (Derivation body Gamma (equal (numeral 1) (numeral 1))) :=
    ⟨by simpa only [equalEqn] using (InternalTagArithmeticSupportProof.refl (numeral 1))⟩
  exact applicationNodeEquation _ _ _ raw parameter typ htyp htag
    (dispatchTwoValue data.oldSource (sourceCheck data) (numeral 1) raw parameter htag he)
    (dispatchTwoValue data.oldTarget lambdaShape (numeral 1) raw parameter htag he)

theorem targetApplicationNode (data : InternalOriginalUniformDescentSelection.Data)
    (raw parameter typ : OTerm alpha)
    (htyp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ raw)))
    (htag : Nonempty (Derivation body Gamma (TagIs 2 raw))) :
    Nonempty (Derivation body Gamma
      ((NodeFactors (targetRoot data) (InternalLessThan.constantOne 2)
        (InternalLessThan.constantOne 2) raw parameter).iff
        (graph2 (InternalLessThan.constantOne 2) (numeral 1) typ parameter))) := by
  have he : Nonempty (Derivation body Gamma (equal (numeral 1) (numeral 1))) :=
    ⟨by simpa only [equalEqn] using (InternalTagArithmeticSupportProof.refl (numeral 1))⟩
  exact applicationNodeEquation _ _ _ raw parameter typ htyp htag
    (dispatchTwoValue data.oldTarget lambdaShape (numeral 1) raw parameter htag he)
    (InternalLessThanSupportProof.oneConstantValue (Fin.cons raw (Fin.cons parameter Fin.elim0)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationNodeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationNodeProof
