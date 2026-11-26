module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidityTagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidityRecurrenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalNodeSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceFactorSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceProof (recurrenceIff)
open OriginalHereditaryValidityInternalRecurrenceOutputProof (actualOriginalHereditaryInternalValidatorOutput)
open OriginalTransparentLambdaValidityInternal (TagIs BooleanOutput)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalTransparentLambdaFinalLogicProof (iffCompose booleanIff)
open OriginalFinalOtherValidityTagProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The original node witness block is constructed, not supplied externally. -/
theorem nodeAtTag (s t m : Program 2) (raw parameter typ tag : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (graph2 s (numeral 1) raw parameter)))
    (ht : Nonempty (Derivation body Gamma (graph2 t (numeral 1) raw parameter)))
    (htyp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ raw)))
    (htag : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag tag raw)))
    (hn2 : Nonempty (Derivation body Gamma (equal tag (numeral 2)).not)) :
    Nonempty (Derivation body Gamma (NodeFactors s t m raw parameter)) := by
  let E := equal tag (numeral 2)
  obtain ⟨hn2⟩ := addAssumption hn2 E
  have hm : Nonempty (Derivation body Gamma (E.imp (graph2 m (numeral 1) typ parameter))) :=
    ⟨Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination hn2 (Derivation.hypothesis List.mem_cons_self)))⟩
  exact andIntro hs (andIntro ht
    (fieldsIntro m raw parameter typ tag (andIntro htyp (andIntro htag hm))))

/-- Both child implications and the membership implication are discharged
by the original tag exclusions. No child validity or run is a premise. -/
theorem recurrenceOtherEquation (s t m : Program 2) (raw parameter : OTerm alpha)
    (h2 : Nonempty (Derivation body Gamma (TagIs 2 raw).not))
    (h1 : Nonempty (Derivation body Gamma (TagIs 1 raw).not)) :
    Nonempty (Derivation body Gamma
      ((RecurrenceFactors s t m raw parameter).iff
        (graph2 s (numeral 1) raw parameter ⊓ graph2 t (numeral 1) raw parameter))) := by
  let R := RecurrenceFactors s t m raw parameter
  let F := graph2 s (numeral 1) raw parameter ⊓ graph2 t (numeral 1) raw parameter
  have hr : Nonempty (Derivation body (R :: Gamma) R) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := andIntro (andLeft (andLeft hr)) (andLeft (andRight (andLeft hr)))
  have hb : Nonempty (Derivation body (F :: Gamma) R) := by
    have hf : Nonempty (Derivation body (F :: Gamma) F) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have h2f := addAssumption h2 F
    have h1f := addAssumption h1 F
    apply queryCases (![InternalUnpair.left,OriginalLambdaConstructor.tag] : Fin 2 → Program 1)
      (Fin.cons raw Fin.elim0) _
    intro beta j DeltaValues Theta hj hq
    rw [recurrenceRename]
    have hs' := renameInto (andLeft hf) j Theta hj
    have ht' := renameInto (andRight hf) j Theta hj
    simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hs' ht'
    have h2' := renameInto h2f j Theta hj
    have h1' := renameInto h1f j Theta hj
    change Nonempty (Derivation body Theta ((TagIs 2 raw).relabel j).not) at h2'
    change Nonempty (Derivation body Theta ((TagIs 1 raw).relabel j).not) at h1'
    simp only [TagIs,graph1Rename,numeral,sucRelabel,zRelabel] at h2' h1'
    have htyp : Nonempty (Derivation body Theta
        (graph1 InternalUnpair.left (DeltaValues 0) (raw.relabel j))) := by
      simpa only [Matrix.cons_val_zero,consTermRename,emptyRename] using hq 0
    have htag : Nonempty (Derivation body Theta
        (graph1 OriginalLambdaConstructor.tag (DeltaValues 1) (raw.relabel j))) := by
      simpa only [Matrix.cons_val_one,Matrix.cons_val_zero,consTermRename,emptyRename] using hq 1
    have hn2 := tagValueNot 2 (raw.relabel j) (DeltaValues 1) htag h2'
    have hn1 := tagValueNot 1 (raw.relabel j) (DeltaValues 1) htag h1'
    have hn := nodeAtTag s t m (raw.relabel j) (parameter.relabel j)
      (DeltaValues 0) (DeltaValues 1) hs' ht' htyp htag hn2
    let E2 := equal (DeltaValues 1) (numeral 2)
    let E1 := equal (DeltaValues 1) (numeral 1)
    obtain ⟨hne2⟩ := addAssumption hn2 E2
    obtain ⟨hne1⟩ := addAssumption hn1 E1
    have ha : Nonempty (Derivation body Theta
        (E2.imp (RootApplicationChildren s t m (raw.relabel j) (parameter.relabel j)))) :=
      ⟨Derivation.implicationIntroduction (Derivation.explosion
        (Derivation.implicationElimination hne2 (Derivation.hypothesis List.mem_cons_self)))⟩
    have hl : Nonempty (Derivation body Theta
        (E1.imp (RootLambdaChild s t m (raw.relabel j) (parameter.relabel j)))) :=
      ⟨Derivation.implicationIntroduction (Derivation.explosion
        (Derivation.implicationElimination hne1 (Derivation.hypothesis List.mem_cons_self)))⟩
    exact recurrenceIntro s t m (raw.relabel j) (parameter.relabel j) (DeltaValues 1)
      hn (andIntro htag (andIntro ha hl))
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem acceptanceOtherEquation (s t m : Program 2) (raw parameter : OTerm alpha)
    (h2 : Nonempty (Derivation body Gamma (TagIs 2 raw).not))
    (h1 : Nonempty (Derivation body Gamma (TagIs 1 raw).not)) :
    Nonempty (Derivation body Gamma
      ((graph2 (validator s t m) (numeral 1) raw parameter).iff
        (graph2 s (numeral 1) raw parameter ⊓ graph2 t (numeral 1) raw parameter))) :=
  iffCompose (recurrenceIff s t m raw parameter) (recurrenceOtherEquation s t m raw parameter h2 h1)

/-- Specialize the accepted full-output hereditary recurrence, not a
native computation or a Boolean assumption about arbitrary leaves. -/
theorem outputOtherEquation (s t m : Program 2) (out raw parameter : OTerm alpha)
    (h2 : Nonempty (Derivation body Gamma (TagIs 2 raw).not))
    (h1 : Nonempty (Derivation body Gamma (TagIs 1 raw).not)) :
    Nonempty (Derivation body Gamma
      ((graph2 (validator s t m) out raw parameter).iff
        (BooleanOutput out
          (graph2 s (numeral 1) raw parameter ⊓ graph2 t (numeral 1) raw parameter)))) := by
  obtain ⟨h⟩ := actualOriginalHereditaryInternalValidatorOutput body s t m alpha out raw parameter
  exact iffCompose ⟨InternalPositiveUnfoldingSupportProof.weakenClosed h Gamma⟩
    (booleanIff out (recurrenceOtherEquation s t m raw parameter h2 h1))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidityRecurrenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidityRecurrenceProof
