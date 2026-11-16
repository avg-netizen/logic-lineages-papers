module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.LambdaSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.TagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.CrossProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalNumberedEnumerationBranch.CrossIntroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.LambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open OriginalEncodedNumberedEnumerationBranch
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem forwardAt (types opened out code pairs : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (OriginalEnumerationConstructorLayer.tagPayload 1)) out pairs)))
    (hp : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross pairs types opened)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (Targets.lambdaCase types opened code)) := by
  have hi := MapElimProof.recover (OriginalEnumerationConstructorLayer.tagPayload 1) pairs out code hg hm
  apply MapImageEliminationProof.cases (OriginalEnumerationConstructorLayer.tagPayload 1) pairs code _ hi
  intro beta j Theta payload hj hmem htag
  rw [LambdaSyntaxProof.caseRename]
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  rw [graph2Rename] at hpj
  apply OriginalDecodedRank.SupportProof.pairCases payload _
  intro gamma k Xi t child hk hpair
  rw [LambdaSyntaxProof.caseRename]
  have hpk := InternalGraphCompositionFunctionalityProof.renameInto hpj k Xi hk
  rw [graph2Rename] at hpk
  have hmk := InternalGraphCompositionFunctionalityProof.renameInto hmem k Xi hk
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmk
  have htk := InternalGraphCompositionFunctionalityProof.renameInto htag k Xi hk
  rw [graph1Rename] at htk
  have hmembers := NumericDependencyCross.CrossProof.projection
    ((types.relabel j).relabel k) ((opened.relabel j).relabel k)
    ((pairs.relabel j).relabel k) (payload.relabel k) t child hpk hmk hpair
  have hc := TagProof.introduce 1 TagProof.binaryPayload ![t,child]
    ((code.relabel j).relabel k) (payload.relabel k) (TagProof.binaryAt t child _ hpair) htk
  exact LambdaSyntaxProof.introduce ((types.relabel j).relabel k)
    ((opened.relabel j).relabel k) ((code.relabel j).relabel k) ![t,child] (andIntro hmembers hc)

theorem backwardAt (types opened out code pairs : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (OriginalEnumerationConstructorLayer.tagPayload 1)) out pairs)))
    (hp : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross pairs types opened)))
    (hw : Nonempty (Derivation body Delta (Targets.lambdaCase types opened code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  apply LambdaSyntaxProof.cases types opened code _ hw
  intro beta j Theta ys hj hf
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  rw [graph2Rename] at hpj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [graph1Rename] at hgj
  apply programCases InternalPairing.pairing (Fin.cons (ys 0) (Fin.cons (ys 1) Fin.elim0)) _
  intro gamma k Xi payload hk hpair
  simp only [consTermRename,emptyRename] at hpair
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hpk := InternalGraphCompositionFunctionalityProof.renameInto hpj k Xi hk
  rw [graph2Rename] at hpk
  have hgk := InternalGraphCompositionFunctionalityProof.renameInto hgj k Xi hk
  rw [graph1Rename] at hgk
  have hfk := InternalGraphCompositionFunctionalityProof.renameInto hf k Xi hk
  rw [LambdaSyntaxProof.fieldsRename] at hfk
  have hmem := OriginalNumberedEnumerationBranch.CrossIntroProof.introduce
    ((types.relabel j).relabel k) ((opened.relabel j).relabel k)
    ((pairs.relabel j).relabel k) payload ((ys 0).relabel k) ((ys 1).relabel k) hpk (andLeft hfk) hpair
  have htag := TagProof.recover 1 TagProof.binaryPayload ![(ys 0).relabel k,(ys 1).relabel k]
    ((code.relabel j).relabel k) payload (TagProof.binaryAt _ _ _ hpair) (andRight hfk)
  exact MapIntroProof.introduce (OriginalEnumerationConstructorLayer.tagPayload 1)
    ((pairs.relabel j).relabel k) z ((out.relabel j).relabel k) ((code.relabel j).relabel k) z payload hgk hmem htag

theorem pairsAt (xs : Fin 7 → OTerm alpha) (pairs : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.lambdaPairs pairs xs))) :
    Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross pairs (xs 0) (xs 6))) :=
  binaryRecover NumericDependencyCross.cross (.projection 0) (.projection 6)
    pairs (xs 0) (xs 6) xs hp (projectionValue 0 xs) (projectionValue 6 xs)

theorem mapAt (xs : Fin 7 → OTerm alpha) (out pairs : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.lambdas out xs)))
    (hp : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.lambdaPairs pairs xs))) :
    Nonempty (Derivation body Delta (graph1 (InternalListMap.map (OriginalEnumerationConstructorLayer.tagPayload 1)) out pairs)) :=
  unaryRecover (InternalListMap.map (OriginalEnumerationConstructorLayer.tagPayload 1))
    OriginalEnumerationConstructorLayer.lambdaPairs out pairs xs hg hp

theorem forward (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.lambdas out xs)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (Targets.lambdaCase (xs 0) (xs 6) code)) := by
  apply programCases OriginalEnumerationConstructorLayer.lambdaPairs xs _
  intro beta j Theta pairs hj hp
  rw [LambdaSyntaxProof.caseRename]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [programRename] at hgj
  have hxj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hxj
  exact forwardAt ((xs 0).relabel j) ((xs 6).relabel j) (out.relabel j) (code.relabel j) pairs
    (mapAt (fun i => (xs i).relabel j) (out.relabel j) pairs hgj hp)
    (pairsAt (fun i => (xs i).relabel j) pairs hp) hxj

theorem backward (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.lambdas out xs)))
    (hw : Nonempty (Derivation body Delta (Targets.lambdaCase (xs 0) (xs 6) code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  apply programCases OriginalEnumerationConstructorLayer.lambdaPairs xs _
  intro beta j Theta pairs hj hp
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [programRename] at hgj
  have hxj := InternalGraphCompositionFunctionalityProof.renameInto hw j Theta hj
  rw [LambdaSyntaxProof.caseRename] at hxj
  exact backwardAt ((xs 0).relabel j) ((xs 6).relabel j) (out.relabel j) (code.relabel j) pairs
    (mapAt (fun i => (xs i).relabel j) (out.relabel j) pairs hgj hp)
    (pairsAt (fun i => (xs i).relabel j) pairs hp) hxj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.LambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.LambdaProof
