module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackWiringProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedCanonicalResultFold InternalApplicationCertificateConstructors
open InternalStrongInduction SourceComputabilityFormulaSupportProof
open InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem sourcePremisesSubst {α β : Type} (data : Data)
    (input typ parameter : OTerm α) (ts : α → OTerm β) :
    (sourcePremises data input typ parameter).subst (fun a => emb (ts a)) =
      sourcePremises data (input.subst ts) (typ.subst ts) (parameter.subst ts) := by
  simp only [sourcePremises,conjunctionSubst,graph2,graph1,programSubst,consTermSubst,emptySubst,InternalOriginalStepGuard.one,sucSubst,zSubst]

theorem certifiedResultSubst {α β : Type} (data : Data)
    (out input parameter : OTerm α) (ts : α → OTerm β) :
    (certifiedResult data out input parameter).subst (fun a => emb (ts a)) =
      certifiedResult data (out.subst ts) (input.subst ts) (parameter.subst ts) := by
  simp only [certifiedResult,InternalParameterizedApplicationCertifiedResultFoldClosure.certifiedFoldP,conjunctionSubst,graph2,programSubst,consTermSubst,emptySubst,InternalOriginalStepGuard.one,sucSubst,zSubst]

theorem outputInvariantSubst {α β : Type} (data : Data)
    (out typ parameter : OTerm α) (ts : α → OTerm β) :
    (outputInvariant data out typ parameter).subst (fun a => emb (ts a)) =
      outputInvariant data (out.subst ts) (typ.subst ts) (parameter.subst ts) := by
  simp only [outputInvariant,InternalOriginalUniformDescentSelection.outputInvariant,conjunctionSubst,
    InternalParameterizedBoundedDescentNormalizerSyntaxProof.validSubst,
    InternalParameterizedBoundedDescentNormalizerSyntaxProof.leftSubst,
    InternalParameterizedBoundedDescentNormalizerSyntaxProof.transitionSubst]

theorem certifiedOutputSubst {α β : Type} (data : Data)
    (out input typ parameter : OTerm α) (ts : α → OTerm β) :
    (certifiedOutput data out input typ parameter).subst (fun a => emb (ts a)) =
      certifiedOutput data (out.subst ts) (input.subst ts) (typ.subst ts) (parameter.subst ts) := by
  simp only [certifiedOutput,conjunctionSubst,certifiedResultSubst,outputInvariantSubst]

theorem foldGraphSubst {α β : Type} (data : Data)
    (out input parameter : OTerm α) (ts : α → OTerm β) :
    (foldGraph data out input parameter).subst (fun a => emb (ts a)) =
      foldGraph data (out.subst ts) (input.subst ts) (parameter.subst ts) := by
  simp only [foldGraph,graph2,programSubst,consTermSubst,emptySubst]

theorem goodRunAcceptedSubst {α β : Type} (data : Data)
    (input parameter : OTerm α) (ts : α → OTerm β) :
    (goodRunAccepted data input parameter).subst (fun a => emb (ts a)) =
      goodRunAccepted data (input.subst ts) (parameter.subst ts) := by
  simp only [goodRunAccepted,graph2,programSubst,consTermSubst,emptySubst,InternalOriginalStepGuard.one,sucSubst,zSubst]

theorem successfulOutputSubst {α β : Type} (data : Data)
    (out input typ parameter : OTerm α) (ts : α → OTerm β) :
    (successfulOutput data out input typ parameter).subst (fun a => emb (ts a)) =
      successfulOutput data (out.subst ts) (input.subst ts) (typ.subst ts) (parameter.subst ts) := by
  simp only [successfulOutput,conjunctionSubst,goodRunAcceptedSubst,outputInvariantSubst]

theorem typedOutputSubst {α β : Type} (data : Data)
    (out input typ parameter : OTerm α) (ts : α → OTerm β) :
    (typedOutput data out input typ parameter).subst (fun a => emb (ts a)) =
      typedOutput data (out.subst ts) (input.subst ts) (typ.subst ts) (parameter.subst ts) := by
  simp only [typedOutput,conjunctionSubst,goodRunAcceptedSubst,InternalOriginalUniformDescentSelection.typedAccepted,graph3,programSubst,consTermSubst,emptySubst,InternalOriginalStepGuard.one,sucSubst,zSubst]

@[simp] theorem sourcePremisesRename {α β : Type} (data : Data)
    (input typ parameter : OTerm α) (j : α → β) :
    (sourcePremises data input typ parameter).relabel j =
      sourcePremises data (input.relabel j) (typ.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (sourcePremises data input typ parameter).subst (fun a => emb (.var (j a))) = _
  rw [sourcePremisesSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem certifiedResultRename {α β : Type} (data : Data)
    (out input parameter : OTerm α) (j : α → β) :
    (certifiedResult data out input parameter).relabel j =
      certifiedResult data (out.relabel j) (input.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (certifiedResult data out input parameter).subst (fun a => emb (.var (j a))) = _
  rw [certifiedResultSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem outputInvariantRename {α β : Type} (data : Data)
    (out typ parameter : OTerm α) (j : α → β) :
    (outputInvariant data out typ parameter).relabel j =
      outputInvariant data (out.relabel j) (typ.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (outputInvariant data out typ parameter).subst (fun a => emb (.var (j a))) = _
  rw [outputInvariantSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem certifiedOutputRename {α β : Type} (data : Data)
    (out input typ parameter : OTerm α) (j : α → β) :
    (certifiedOutput data out input typ parameter).relabel j =
      certifiedOutput data (out.relabel j) (input.relabel j) (typ.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (certifiedOutput data out input typ parameter).subst (fun a => emb (.var (j a))) = _
  rw [certifiedOutputSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem foldGraphRename {α β : Type} (data : Data)
    (out input parameter : OTerm α) (j : α → β) :
    (foldGraph data out input parameter).relabel j =
      foldGraph data (out.relabel j) (input.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (foldGraph data out input parameter).subst (fun a => emb (.var (j a))) = _
  rw [foldGraphSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem goodRunAcceptedRename {α β : Type} (data : Data)
    (input parameter : OTerm α) (j : α → β) :
    (goodRunAccepted data input parameter).relabel j =
      goodRunAccepted data (input.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (goodRunAccepted data input parameter).subst (fun a => emb (.var (j a))) = _
  rw [goodRunAcceptedSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem successfulOutputRename {α β : Type} (data : Data)
    (out input typ parameter : OTerm α) (j : α → β) :
    (successfulOutput data out input typ parameter).relabel j =
      successfulOutput data (out.relabel j) (input.relabel j) (typ.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (successfulOutput data out input typ parameter).subst (fun a => emb (.var (j a))) = _
  rw [successfulOutputSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem typedOutputRename {α β : Type} (data : Data)
    (out input typ parameter : OTerm α) (j : α → β) :
    (typedOutput data out input typ parameter).relabel j =
      typedOutput data (out.relabel j) (input.relabel j) (typ.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (typedOutput data out input typ parameter).subst (fun a => emb (.var (j a))) = _
  rw [typedOutputSubst]
  simp only [← termRelabelAsSubst]

theorem hasCertifiedOutputSubst {α β : Type} (data : Data)
    (input typ parameter : OTerm α) (ts : α → OTerm β) :
    (hasCertifiedOutput data input typ parameter).subst (fun a => emb (ts a)) =
      hasCertifiedOutput data (input.subst ts) (typ.subst ts) (parameter.subst ts) := by
  unfold hasCertifiedOutput
  rw [existsSubst,liftedEmbedding,certifiedOutputSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem hasCertifiedOutputRename {α β : Type} (data : Data)
    (input typ parameter : OTerm α) (j : α → β) :
    (hasCertifiedOutput data input typ parameter).relabel j =
      hasCertifiedOutput data (input.relabel j) (typ.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (hasCertifiedOutput data input typ parameter).subst (fun a => emb (.var (j a))) = _
  rw [hasCertifiedOutputSubst]
  simp only [← termRelabelAsSubst]

theorem certifiedOutputInstantiate {α : Type} (data : Data)
    (out input typ parameter : OTerm α) :
    instantiate (certifiedOutput data (.var (.inr 0))
      (input.relabel Sum.inl) (typ.relabel Sum.inl) (parameter.relabel Sum.inl)) (emb out) =
      certifiedOutput data out input typ parameter := by
  rw [instantiate,bindEmbedding,certifiedOutputSubst]
  simp only [varBind,liftBind]

theorem atPayloadSubst {α β : Type} (data : Data)
    (payload : OTerm α) (ts : α → OTerm β) :
    (atPayload data payload).subst (fun a => emb (ts a)) =
      atPayload data (payload.subst ts) := by
  unfold atPayload payloadMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    sourcePremisesSubst,hasCertifiedOutputSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atPayloadRename {α β : Type} (data : Data)
    (payload : OTerm α) (j : α → β) :
    (atPayload data payload).relabel j = atPayload data (payload.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (atPayload data payload).subst (fun a => emb (.var (j a))) = _
  rw [atPayloadSubst]
  simp only [← termRelabelAsSubst]

theorem payloadMatrixWitness {α : Type} (data : Data)
    (payload input typ parameter : OTerm α) :
    (payloadMatrix data payload).subst
      (Sum.elim Term.var (fun i => emb (![input,typ,parameter] i))) =
      (graph1 InternalUnpair.right payload input).imp
        ((sourcePremises data input typ parameter).imp
          (hasCertifiedOutput data input typ parameter)) := by
  have he : (Sum.elim Term.var (fun i => emb (![input,typ,parameter] i))) =
      (fun a => emb (Sum.elim Term.var ![input,typ,parameter] a)) := by
    funext a
    cases a <;> rfl
  unfold payloadMatrix
  rw [he]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    sourcePremisesSubst,hasCertifiedOutputSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

def payloadPredicate (data : Data) {α : Type} : Formula (α ⊕ Fin 1) :=
  atPayload data (.var (.inr 0))

def belowPayload {α : Type} (data : Data) (payload : OTerm α) : Formula α :=
  InternalStrongInduction.below (payloadPredicate data) payload

theorem payloadPredicateInstantiate {α : Type} (data : Data) (payload : OTerm α) :
    instantiate (payloadPredicate data) (emb payload) = atPayload data payload := by
  rw [payloadPredicate,instantiate,bindEmbedding,atPayloadSubst]
  simp only [varBind]

@[simp] theorem belowPayloadRename {α β : Type} (data : Data)
    (payload : OTerm α) (j : α → β) :
    (belowPayload data payload).relabel j = belowPayload data (payload.relabel j) := by
  unfold belowPayload
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold payloadPredicate
  rw [atPayloadRename]
  rfl

theorem payloadPredicateLift {α : Type} (data : Data) :
    lift (payloadPredicate data (α := α)) =
      payloadPredicate data (α := α ⊕ Fin 1) := by
  unfold lift payloadPredicate
  rw [atPayloadRename]
  rfl

@[simp] theorem applicationGraphRename {α β : Type} (data : Data)
    (out d e x a parameter : OTerm α) (j : α → β) :
    (applicationGraph data out d e x a parameter).relabel j =
      applicationGraph data (out.relabel j) (d.relabel j) (e.relabel j)
        (x.relabel j) (a.relabel j) (parameter.relabel j) := by
  change (programGraph (actualJ data) out
    (Fin.cons d (Fin.cons e (Fin.cons x (Fin.cons a (Fin.cons parameter Fin.elim0)))))).relabel j =
      programGraph (actualJ data) (out.relabel j)
        (Fin.cons (d.relabel j) (Fin.cons (e.relabel j) (Fin.cons (x.relabel j)
          (Fin.cons (a.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)))))
  simp only [programRename,consTermRename,emptyRename]

@[simp] theorem representativePremisesRename {α β : Type} (data : Data)
    (arrow d e fn arg parent x out parameter : OTerm α) (j : α → β) :
    (representativePremises data arrow d e fn arg parent x out parameter).relabel j =
      representativePremises data (arrow.relabel j) (d.relabel j) (e.relabel j)
        (fn.relabel j) (arg.relabel j) (parent.relabel j) (x.relabel j)
        (out.relabel j) (parameter.relabel j) := by
  simp only [representativePremises,conjunctionRename,
    InternalApplicationCertificateConstructorsSyntaxProof.graph2Rename,
    InternalApplicationCertificateConstructorsSyntaxProof.graph1Rename,
    InternalApplicationCertificateConstructorsSyntaxProof.graph4Rename,
    foldGraphRename,applicationGraphRename,InternalOriginalStepGuard.one,sucRelabel,zRelabel]

@[simp] theorem representativeConclusionRename {α β : Type} (data : Data)
    (parent out e parameter : OTerm α) (j : α → β) :
    (representativeConclusion data parent out e parameter).relabel j =
      representativeConclusion data (parent.relabel j) (out.relabel j)
        (e.relabel j) (parameter.relabel j) := by
  simp only [representativeConclusion,conjunctionRename,
    InternalApplicationCertificateConstructorsSyntaxProof.graph2Rename,
    certifiedOutputRename,InternalOriginalStepGuard.one,sucRelabel,zRelabel]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldSyntaxProof

