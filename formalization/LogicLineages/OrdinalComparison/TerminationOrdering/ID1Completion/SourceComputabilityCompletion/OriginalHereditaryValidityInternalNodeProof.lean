module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalNodeSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalStateSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalNodeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalHereditaryValidityInternalNodeSyntaxProof OriginalHereditaryValidityInternalNodeSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalGraphCompositionFunctionalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem recoverFactors (s t m : Program 2) (state raw parameter : OTerm α)
    (hr : Nonempty (Derivation body Gamma (graph1 currentRaw raw state)))
    (hp : Nonempty (Derivation body Gamma (graph1 currentParameter parameter state)))
    (hn : Nonempty (Derivation body Gamma (graph1 (nodeCheck s t m) (numeral 1) state))) :
    Nonempty (Derivation body Gamma (NodeFactors s t m raw parameter)) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have hc := conjunctionRecover (exactOne (.composition s ![currentRaw,currentParameter])) _ xs hn
  have hd := conjunctionRecover (exactOne (.composition t ![currentRaw,currentParameter])) _ xs (andRight hc)
  have hs := binaryRecover s currentRaw currentParameter (numeral 1) raw parameter xs
    (exactRecover _ xs (andLeft hc)) hr hp
  have ht := binaryRecover t currentRaw currentParameter (numeral 1) raw parameter xs
    (exactRecover _ xs (andLeft hd)) hr hp
  apply andIntro hs
  apply andIntro ht
  change Nonempty (Derivation body Gamma (someFields m raw parameter))
  apply queryCases ![InternalUnpair.left,OriginalLambdaConstructor.tag] (Fin.cons raw Fin.elim0) _
  intro β j ys Delta hj hq
  have hr' := renameInto hr j Delta hj
  have hp' := renameInto hp j Delta hj
  have hn' := renameInto hn j Delta hj
  simp only [graph1Rename,numeral,sucRelabel,zRelabel] at hr' hp' hn'
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hq
  simp only [someFieldsRename]
  exact fieldsIntro m (raw.relabel j) (parameter.relabel j) (ys 0) (ys 1)
    (recoverFields s t m (state.relabel j) (raw.relabel j) (parameter.relabel j) (ys 0) (ys 1)
      hr' hp' (hq 0) (hq 1) hn')

theorem acceptFactors (s t m : Program 2) (state raw parameter : OTerm α)
    (hr : Nonempty (Derivation body Gamma (graph1 currentRaw raw state)))
    (hp : Nonempty (Derivation body Gamma (graph1 currentParameter parameter state)))
    (hf : Nonempty (Derivation body Gamma (NodeFactors s t m raw parameter))) :
    Nonempty (Derivation body Gamma (graph1 (nodeCheck s t m) (numeral 1) state)) := by
  apply fieldsCases m raw parameter _ (andRight (andRight hf))
  intro β j Delta typ tag hj hfields
  have hr' := renameInto hr j Delta hj
  have hp' := renameInto hp j Delta hj
  have hf' := renameInto hf j Delta hj
  simp only [graph1Rename] at hr' hp'
  simp only [factorsRename] at hf'
  simp only [graph1Rename,numeral,sucRelabel,zRelabel]
  exact acceptAtFields s t m (state.relabel j) (raw.relabel j) (parameter.relabel j) typ tag
    hr' hp' (andLeft hf') (andLeft (andRight hf')) hfields

theorem nodeAtSelectors (s t m : Program 2) (state raw parameter : OTerm α)
    (hr : Nonempty (Derivation body Gamma (graph1 currentRaw raw state)))
    (hp : Nonempty (Derivation body Gamma (graph1 currentParameter parameter state))) :
    Nonempty (Derivation body Gamma ((graph1 (nodeCheck s t m) (numeral 1) state).iff
      (NodeFactors s t m raw parameter))) := by
  let A := graph1 (nodeCheck s t m) (numeral 1) state
  let B := NodeFactors s t m raw parameter
  obtain ⟨hf⟩ := recoverFactors s t m state raw parameter
    (weakenProof hr (fun p hp => List.mem_cons_of_mem A hp))
    (weakenProof hp (fun p hp => List.mem_cons_of_mem A hp))
    (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := acceptFactors s t m state raw parameter
    (weakenProof hr (fun p hp => List.mem_cons_of_mem B hp))
    (weakenProof hp (fun p hp => List.mem_cons_of_mem B hp))
    (show Nonempty (Derivation body (B :: Gamma) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem actualOriginalHereditaryNodeGraph :
    OriginalHereditaryValidityInternalTargets.ActualOriginalHereditaryNodeGraph := by
  intro body s t m α state raw parameter
  let P := graph1 currentRaw raw state ⊓ graph1 currentParameter parameter state
  have hp : Nonempty (Derivation body [P] P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := nodeAtSelectors s t m state raw parameter (andLeft hp) (andRight hp)
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualOriginalHereditaryInitialNodeGraph :
    OriginalHereditaryValidityInternalTargets.ActualOriginalHereditaryInitialNodeGraph := by
  intro body s t m α state raw parameter
  let P := graph2 initial state raw parameter
  have hp : Nonempty (Derivation body [P] P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hs := OriginalHereditaryValidityInternalStateSupportProof.initialSelectors state raw parameter hp
  obtain ⟨h⟩ := nodeAtSelectors s t m state raw parameter (andLeft hs) (andRight hs)
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalNodeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalNodeProof
