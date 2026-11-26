module
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectSyntaxProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalVariableObject SourceComputabilityFormulaSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalComputabilityApplicationSyntaxProof InternalDerivationRenamingSyntaxProof
open InternalRecursionGraphStepSyntaxProof InternalRecursionClosureSyntaxProof
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalControlGraphSupportProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open GuardedSourceSyntaxProof (numeralRename)
open InternalTagArithmeticSyntaxProof (OTerm emb bindEmbedding liftBind varBind zRelabel sucRelabel)

theorem variableObjectRename {α β : Type} (object : OTerm α) (j : α → β) :
    (variableObject object).relabel j = variableObject (object.relabel j) := by
  simp only [variableObject,graph1Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel]

theorem bottomGraphRename {α β : Type} (out typ gammaCode : OTerm α) (j : α → β) :
    (ComputabilityLeast.bottomGraph out typ gammaCode).relabel j =
      ComputabilityLeast.bottomGraph (out.relabel j) (typ.relabel j) (gammaCode.relabel j) := by
  rw [ComputabilityLeast.bottomGraph,graph2Rename]
  rfl

theorem bottomAtSourceGammaRename {α β : Type} (tau : Ty) (source target : OTerm α)
    (j : α → β) :
    (bottomAtSourceGamma tau source target).relabel j =
      bottomAtSourceGamma tau (source.relabel j) (target.relabel j) := by
  unfold bottomAtSourceGamma
  rw [existsRename]
  simp only [conjunctionRename,graph1Rename,bottomGraphRename,numeralRename,Term.relabel_relabel]
  rfl

theorem bottomAtSourceGammaInstance {α : Type} (tau : Ty) (source target gammaCode : OTerm α) :
    instantiate
      (graph1 InternalUnpair.left (.var (.inr (0 : Fin 1))) (source.relabel Sum.inl) ⊓
        ComputabilityLeast.bottomGraph (target.relabel Sum.inl)
          (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) (.var (.inr 0)))
      (emb gammaCode) =
    graph1 InternalUnpair.left gammaCode source ⊓
      ComputabilityLeast.bottomGraph target
        (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) gammaCode := by
  rw [instantiate,bindEmbedding]
  simp only [conjunctionSubst,ComputabilityLeast.bottomGraph,graph1,graph2,
    InternalComputabilityApplicationSyntaxProof.programSubst,consTermSubst,emptySubst,
    liftBind,varBind,numeralSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectSyntaxProof
