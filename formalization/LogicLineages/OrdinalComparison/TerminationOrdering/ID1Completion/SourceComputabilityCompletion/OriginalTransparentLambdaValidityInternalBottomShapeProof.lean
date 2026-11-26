module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceValidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBottomShapeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (cancelSuc sucNeZeroApply)
open InternalBetaTotalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalNodeSyntaxProof
open OriginalTransparentLambdaValidityInternal OriginalTransparentLambdaValidityInternalLambdaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem bottomTag (raw : OTerm alpha)
    (hb : Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) raw))) :
    Nonempty (Derivation body Gamma (TagIs 3 raw)) := by
  apply programCases InternalUnpair.left (Fin.cons raw Fin.elim0) _
  intro beta j Delta typ hj htyp
  have hb' := renameInto hb j Delta hj
  simp only [BottomRepresentative.bottomGraph,graph1Rename,numeral,sucRelabel,zRelabel] at hb'
  simp only [consTermRename,emptyRename] at htyp
  simp only [TagIs,graph1Rename,numeral,sucRelabel,zRelabel]
  exact BottomSourceValidityProof.bottomConstructorTag (raw.relabel j) typ
    (BottomSourceShapeProof.bottomRecover (raw.relabel j) typ htyp hb')

theorem threeNeTwo : Nonempty (Derivation body Gamma
    (equal (numeral 3 : OTerm alpha) (numeral 2)).not) := by
  let E : Formula alpha := equal (numeral 3) (numeral 2)
  have he : Derivation body (E :: Gamma) E := Derivation.hypothesis List.mem_cons_self
  have he' : Derivation body (E :: Gamma)
      (InternalTagArithmeticSyntaxProof.eqn (suc (suc (suc z))) (suc (suc z))) := by
    simpa only [E,equalEqn,numeral] using he
  exact ⟨Derivation.implicationIntroduction
    (sucNeZeroApply (cancelSuc (cancelSuc he')))⟩

theorem threeNeOne : Nonempty (Derivation body Gamma
    (equal (numeral 3 : OTerm alpha) (numeral 1)).not) := by
  let E : Formula alpha := equal (numeral 3) (numeral 1)
  have he : Derivation body (E :: Gamma) E := Derivation.hypothesis List.mem_cons_self
  have he' : Derivation body (E :: Gamma)
      (InternalTagArithmeticSyntaxProof.eqn (suc (suc (suc z))) (suc z)) := by
    simpa only [E,equalEqn,numeral] using he
  exact ⟨Derivation.implicationIntroduction
    (sucNeZeroApply (cancelSuc he'))⟩

theorem tagNotAtThree (k : Nat) (raw : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (TagIs 3 raw)))
    (hne : Nonempty (Derivation body Gamma (equal (numeral 3 : OTerm alpha) (numeral k)).not)) :
    Nonempty (Derivation body Gamma (TagIs k raw).not) := by
  let A := TagIs k raw
  obtain ⟨he⟩ := valueUnique OriginalLambdaConstructor.tag (numeral 3) (numeral k)
    (Fin.cons raw Fin.elim0) (addAssumption ht A)
    (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hne⟩ := addAssumption hne A
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination hne (by simpa only [equalEqn] using he))⟩

theorem bottomNotTwo (raw : OTerm alpha)
    (hb : Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) raw))) :
    Nonempty (Derivation body Gamma (TagIs 2 raw).not) :=
  tagNotAtThree 2 raw (bottomTag raw hb) threeNeTwo

theorem bottomNotOne (raw : OTerm alpha)
    (hb : Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) raw))) :
    Nonempty (Derivation body Gamma (TagIs 1 raw).not) :=
  tagNotAtThree 1 raw (bottomTag raw hb) threeNeOne

theorem nodeAtThree (s t m : Program 2) (raw parameter : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (graph2 s (numeral 1) raw parameter)))
    (ht : Nonempty (Derivation body Gamma (graph2 t (numeral 1) raw parameter)))
    (htag : Nonempty (Derivation body Gamma (TagIs 3 raw))) :
    Nonempty (Derivation body Gamma (NodeFactors s t m raw parameter)) := by
  apply programCases InternalUnpair.left (Fin.cons raw Fin.elim0) _
  intro beta j Delta typ hj htyp
  have hs' := renameInto hs j Delta hj
  have ht' := renameInto ht j Delta hj
  have htag' := renameInto htag j Delta hj
  simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hs' ht'
  simp only [TagIs,graph1Rename,numeral,sucRelabel,zRelabel] at htag'
  simp only [consTermRename,emptyRename] at htyp
  simp only [factorsRename]
  let E : Formula beta := equal (numeral 3) (numeral 2)
  obtain ⟨hn⟩ := (threeNeTwo (body := body) (Gamma := E :: Delta))
  have hm : Nonempty (Derivation body Delta
      (E.imp (graph2 m (numeral 1) typ (parameter.relabel j)))) :=
    ⟨Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination hn (Derivation.hypothesis List.mem_cons_self)))⟩
  exact andIntro hs' (andIntro ht'
    (fieldsIntro m (raw.relabel j) (parameter.relabel j) typ (numeral 3)
      (andIntro htyp (andIntro htag' hm))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBottomShapeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBottomShapeProof
