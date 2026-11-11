module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalPushSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalExtensionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalHereditaryValidityInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open SourceComputabilityFormulaSupportProof (numeral)

open OriginalHereditaryValidityInternalPushSyntaxProof OriginalHereditaryValidity
open InternalApplicationCertificateConstructorsSupportProof
open OriginalLambdaConstructorGraphSyntaxProof InternalGraphCompositionFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def extensionFields {alpha : Type} (raw parameter bodyParameter domain context gamma extended : InternalGraphComposition.OTerm alpha) : Formula alpha :=
  graph1 OriginalLambdaConstructor.domain domain raw ⊓
    (graph2 InternalPairing.pairing parameter context gamma ⊓
      (graph2 InternalListCodec.consCode extended domain gamma ⊓
        graph2 InternalPairing.pairing bodyParameter context extended))

def extensionMatrix {alpha : Type} (raw parameter bodyParameter : InternalGraphComposition.OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  extensionFields (raw.relabel Sum.inl) (parameter.relabel Sum.inl) (bodyParameter.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))

theorem extensionFieldsSubst {alpha beta : Type}
    (raw parameter bodyParameter domain context gamma extended : InternalGraphComposition.OTerm alpha) (ts : alpha → InternalGraphComposition.OTerm beta) :
    (extensionFields raw parameter bodyParameter domain context gamma extended).subst (fun a => emb (ts a)) =
      extensionFields (raw.subst ts) (parameter.subst ts) (bodyParameter.subst ts)
        (domain.subst ts) (context.subst ts) (gamma.subst ts) (extended.subst ts) := by
  simp only [extensionFields,conjunctionSubst,graph1,graph2,programSubst,consTermSubst,emptySubst]

theorem extensionMatrixWitness {alpha : Type}
    (raw parameter bodyParameter domain context gamma extended : InternalGraphComposition.OTerm alpha) :
    (extensionMatrix raw parameter bodyParameter).subst
      (Sum.elim Term.var (fun i => emb (![domain,context,gamma,extended] i))) =
      extensionFields raw parameter bodyParameter domain context gamma extended := by
  unfold extensionMatrix
  rw [witnessEmbedding,extensionFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem extendedParameterIntro {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (raw parameter bodyParameter domain context gamma extended : InternalGraphComposition.OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (extensionFields raw parameter bodyParameter domain context gamma extended))) :
    Nonempty (Derivation body Delta (ExtendedParameter raw parameter bodyParameter)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 4 Delta (extensionMatrix raw parameter bodyParameter)
    (fun i => emb (![domain,context,gamma,extended] i))
  rw [extensionMatrixWitness]
  exact h

theorem extendedParameterSubst {alpha beta : Type}
    (raw parameter bodyParameter : InternalGraphComposition.OTerm alpha) (ts : alpha → InternalGraphComposition.OTerm beta) :
    (ExtendedParameter raw parameter bodyParameter).subst (fun a => emb (ts a)) =
      ExtendedParameter (raw.subst ts) (parameter.subst ts) (bodyParameter.subst ts) := by
  change (InternalFiniteBlocks.block (extensionMatrix raw parameter bodyParameter)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold extensionMatrix
  simp only [extensionFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem extendedParameterRename {alpha beta : Type}
    (raw parameter bodyParameter : InternalGraphComposition.OTerm alpha) (j : alpha → beta) :
    (ExtendedParameter raw parameter bodyParameter).relabel j =
      ExtendedParameter (raw.relabel j) (parameter.relabel j) (bodyParameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (ExtendedParameter raw parameter bodyParameter).subst (fun a => emb (.var (j a))) = _
  rw [extendedParameterSubst]
  simp only [← termRelabelAsSubst]

/-- All extension witnesses are obtained internally from the unchanged selectors. -/
theorem childParameterExtension {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (state raw parameter bodyParameter : InternalGraphComposition.OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 currentRaw raw state)))
    (hp : Nonempty (Derivation body Delta (graph1 currentParameter parameter state)))
    (hb : Nonempty (Derivation body Delta (graph1 childParameter bodyParameter state))) :
    Nonempty (Derivation body Delta (ExtendedParameter raw parameter bodyParameter)) := by
  let context := leftOf currentParameter
  let gamma := rightOf currentParameter
  let extended := consOf currentDomain gamma
  let qs : Fin 4 → Program 1 := ![currentDomain,context,gamma,extended]
  let xs : Fin 1 → InternalGraphComposition.OTerm alpha := Fin.cons state Fin.elim0
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [extendedParameterRename]
  have hr' := renameInto hr j Theta hj
  have hp' := renameInto hp j Theta hj
  have hb' := renameInto hb j Theta hj
  rw [graph1Rename] at hr' hp' hb'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 1 → InternalGraphComposition.OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  have hd := unaryRecover OriginalLambdaConstructor.domain currentRaw
    (ys 0) (raw.relabel j) xx (hq 0) hr'
  have hc := unaryRecover InternalUnpair.left currentParameter
    (ys 1) (parameter.relabel j) xx (hq 1) hp'
  have hg := unaryRecover InternalUnpair.right currentParameter
    (ys 2) (parameter.relabel j) xx (hq 2) hp'
  have he := binaryRecover InternalListCodec.consCode currentDomain gamma
    (ys 3) (ys 0) (ys 2) xx (hq 3) (hq 0) (hq 2)
  have hbody := binaryRecover InternalPairing.pairing context extended
    (bodyParameter.relabel j) (ys 1) (ys 3) xx hb' (hq 1) (hq 3)
  exact extendedParameterIntro _ _ _ (ys 0) (ys 1) (ys 2) (ys 3)
    (andIntro hd (andIntro (reconstructPair _ _ _ hc hg) (andIntro he hbody)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalExtensionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalExtensionProof
