module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalCanonicalResultFoldOpening InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

@[simp] theorem openingAcceptedRename {α β : Type} (valid member : Program 1)
    (parent : OTerm α) (j : α → β) :
    (openingAccepted valid member parent).relabel j =
      openingAccepted valid member (parent.relabel j) := by
  simp only [openingAccepted,graph1Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel]

@[simp] theorem validityFactorsRename {α β : Type} (valid member : Program 1)
    (parent fn arg e : OTerm α) (j : α → β) :
    (validityFactors valid member parent fn arg e).relabel j =
      validityFactors valid member (parent.relabel j) (fn.relabel j)
        (arg.relabel j) (e.relabel j) := by
  simp only [validityFactors,conjunctionRename,graph1Rename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel]

@[simp] theorem originalFieldsRename {α β : Type}
    (parent payload arrow d e fp ap fn arg : OTerm α) (j : α → β) :
    (originalFields parent payload arrow d e fp ap fn arg).relabel j =
      originalFields (parent.relabel j) (payload.relabel j) (arrow.relabel j)
        (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j)
        (fn.relabel j) (arg.relabel j) := by
  simp only [originalFields,conjunctionRename,graph1Rename]

@[simp] theorem openingWitnessesRename {α β : Type} (valid member : Program 1)
    (parent payload middle children arrow d e fp ap fn arg : OTerm α) (j : α → β) :
    (openingWitnesses valid member parent payload middle children arrow d e fp ap fn arg).relabel j =
      openingWitnesses valid member (parent.relabel j) (payload.relabel j)
        (middle.relabel j) (children.relabel j) (arrow.relabel j) (d.relabel j)
        (e.relabel j) (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) := by
  simp only [openingWitnesses,InternalApplicationValidityClosure.applicationConstructors,
    InternalPairingSumBounds.applicationPayloadWitnesses,InternalPairingSumBounds.pairGraph,
    InternalLessThan.strictLess,conjunctionRename,validityFactorsRename,originalFieldsRename,
    programRename,consTermRename,emptyRename,
    sucRelabel,zRelabel,orderRename]

theorem openingWitnessesSubst {α β : Type} (valid member : Program 1)
    (parent payload middle children arrow d e fp ap fn arg : OTerm α) (ts : α → OTerm β) :
    (openingWitnesses valid member parent payload middle children arrow d e fp ap fn arg).subst
      (fun a => emb (ts a)) =
      openingWitnesses valid member (parent.subst ts) (payload.subst ts)
        (middle.subst ts) (children.subst ts) (arrow.subst ts) (d.subst ts)
        (e.subst ts) (fp.subst ts) (ap.subst ts) (fn.subst ts) (arg.subst ts) := by
  simp only [openingWitnesses,InternalApplicationValidityClosure.applicationConstructors,
    validityFactors,originalFields,InternalPairingSumBounds.applicationPayloadWitnesses,
    InternalPairingSumBounds.pairGraph,InternalLessThan.strictLess,
    conjunctionSubst,graph1,graph2,graph4,programSubst,consTermSubst,emptySubst,
    InternalOriginalStepGuard.one,sucSubst,zSubst,orderSubst]

theorem openingMatrixWitness {α : Type} (valid member : Program 1)
    (parent payload middle children arrow d e fp ap fn arg : OTerm α) :
    (openingMatrix valid member parent).subst
      (Sum.elim Term.var (fun i => emb (![payload,middle,children,arrow,d,e,fp,ap,fn,arg] i))) =
      openingWitnesses valid member parent payload middle children arrow d e fp ap fn arg := by
  have he : (Sum.elim Term.var (fun i => emb (![payload,middle,children,arrow,d,e,fp,ap,fn,arg] i))) =
      (fun a => emb (Sum.elim Term.var ![payload,middle,children,arrow,d,e,fp,ap,fn,arg] a)) := by
    funext a
    cases a <;> rfl
  unfold openingMatrix
  rw [he,openingWitnessesSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem openedIntro {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (valid member : Program 1)
    (parent payload middle children arrow d e fp ap fn arg : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (openingWitnesses valid member parent payload middle children arrow d e fp ap fn arg))) :
    Nonempty (Derivation body Gamma (opened valid member parent)) := by
  apply InternalFiniteBlocksProof.introduction body α 10 Gamma (openingMatrix valid member parent)
    (fun i => emb (![payload,middle,children,arrow,d,e,fp,ap,fn,arg] i))
  rw [openingMatrixWitness]
  exact h

theorem openedCases {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (valid member : Program 1) (parent : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (opened valid member parent)))
    (step : ∀ (β : Type) (j : α → β) (Delta : List (Formula β))
      (payload middle children arrow d e fp ap fn arg : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (openingWitnesses valid member (parent.relabel j)
        payload middle children arrow d e fp ap fn arg)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply InternalFiniteBlocksProof.elimination body α 10 Gamma
    (openingMatrix valid member parent) psi h
  apply step (α ⊕ Fin 10) Sum.inl
    (openingMatrix valid member parent :: Gamma.map (fun p => p.relabel Sum.inl))
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))
    (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6)) (.var (.inr 7))
    (.var (.inr 8)) (.var (.inr 9))
  · intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem openedSubst {α β : Type} (valid member : Program 1)
    (parent : OTerm α) (ts : α → OTerm β) :
    (opened valid member parent).subst (fun a => emb (ts a)) =
      opened valid member (parent.subst ts) := by
  unfold opened InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold openingMatrix
  simp only [openingWitnessesSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem openedRename {α β : Type} (valid member : Program 1)
    (parent : OTerm α) (j : α → β) :
    (opened valid member parent).relabel j = opened valid member (parent.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (opened valid member parent).subst (fun a => emb (.var (j a))) = _
  rw [openedSubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningSyntaxProof
