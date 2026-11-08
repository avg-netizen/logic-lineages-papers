module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackInternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStack
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc emb zRelabel sucRelabel bindEmbedding liftBind varBind)
open InternalTagArithmeticSupportProof InternalGraphCompositionFunctionalityProof
open InternalRawListRecursionSyntaxProof
open InternalComputabilityApplicationSyntaxProof InternalGraphCompositionSyntaxProof
open InternalDerivationRenamingSyntaxProof SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Uniform presentation of an internally computed output pushed onto the
arbitrary original result suffix. -/
def returned {n : Nat} (p : Program n) (out : OTerm α) (xs : Fin n → OTerm α)
    (work results : OTerm α) : Formula α :=
  existsOne (programGraph p (.var (.inr (0 : Fin 1))) (fun i => (xs i).relabel Sum.inl) ⊓
    graph3 returnState (out.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
      (work.relabel Sum.inl) (results.relabel Sum.inl))

@[simp] theorem returnedRename {n : Nat} {β : Type} (p : Program n)
    (out : OTerm α) (xs : Fin n → OTerm α) (work results : OTerm α) (j : α → β) :
    (returned p out xs work results).relabel j =
      returned p (out.relabel j) (fun i => (xs i).relabel j)
        (work.relabel j) (results.relabel j) := by
  have hm : (Sum.map j (id : Fin 1 → Fin 1)) ∘ Sum.inl = Sum.inl ∘ j := rfl
  have hv : ((.var (.inr (0 : Fin 1)) : OTerm (α ⊕ Fin 1)).relabel (Sum.map j id)) =
      (.var (.inr (0 : Fin 1)) : OTerm (β ⊕ Fin 1)) := rfl
  simp only [returned,existsRename,conjunctionRename,graph3,programRename,
    consTermRename,emptyRename,Term.relabel_relabel,hm,hv]

theorem returnMatrixInstantiate {n : Nat} (p : Program n)
    (out : OTerm α) (xs : Fin n → OTerm α) (work results value : OTerm α) :
    instantiate (programGraph p (.var (.inr (0 : Fin 1))) (fun i => (xs i).relabel Sum.inl) ⊓
      graph3 returnState (out.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
        (work.relabel Sum.inl) (results.relabel Sum.inl)) (emb value) =
      programGraph p value xs ⊓ graph3 returnState out value work results := by
  rw [instantiate,bindEmbedding]
  change (programGraph p _ _).subst _ ⊓ (graph3 returnState _ _ _ _).subst _ = _
  simp only [graph3,InternalRawListRecursionSyntaxProof.programSubst,consTermSubst,emptySubst,liftBind,varBind]

theorem returnedIntro {n : Nat} (p : Program n) (out : OTerm α)
    (xs : Fin n → OTerm α) (work results value : OTerm α)
    (hp : Nonempty (Derivation body Gamma (programGraph p value xs)))
    (hr : Nonempty (Derivation body Gamma (graph3 returnState out value work results))) :
    Nonempty (Derivation body Gamma (returned p out xs work results)) := by
  obtain ⟨h⟩ := andIntro hp hr
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb value)
  rw [returnMatrixInstantiate]
  exact h

theorem returnedCases {n : Nat} (p : Program n) (out : OTerm α)
    (xs : Fin n → OTerm α) (work results : OTerm α) (psi : Formula α)
    (hr : Nonempty (Derivation body Gamma (returned p out xs work results)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (value : OTerm β),
      (∀ r ∈ Gamma, r.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (programGraph p value (fun i => (xs i).relabel j))) →
      Nonempty (Derivation body Delta (graph3 returnState (out.relabel j) value
        (work.relabel j) (results.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨hr⟩ := hr
  let mat := programGraph p (.var (.inr (0 : Fin 1))) (fun i => (xs i).relabel Sum.inl) ⊓
    graph3 returnState (out.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
      (work.relabel Sum.inl) (results.relabel Sum.inl)
  have hm : Derivation body (mat :: Gamma.map weaken) mat := Derivation.hypothesis List.mem_cons_self
  obtain ⟨hk⟩ := k (α ⊕ Fin 1) Sum.inl (mat :: Gamma.map weaken) (.var (.inr 0))
    (by intro r hr; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,hr,rfl⟩))
    ⟨Derivation.conjunctionLeft hm⟩ ⟨Derivation.conjunctionRight hm⟩
  exact ⟨Derivation.existentialElimination hr hk⟩

/-- Nonzero branch introduction uses the original nonzero formula; it need
not supply a predecessor for a symbolic list code. -/
theorem nonzeroBranchIntro {n : Nat} (control a b : Program n) (out c : OTerm α)
    (xs : Fin n → OTerm α)
    (hc : Nonempty (Derivation body Gamma (programGraph control c xs)))
    (hn : Nonempty (Derivation body Gamma (equal c z).not))
    (hb : Nonempty (Derivation body Gamma (programGraph b out xs))) :
    Nonempty (Derivation body Gamma (programGraph (InternalAcceptance.branch control a b) out xs)) := by
  apply programCases a xs _
  intro β j Delta av hj ha
  simp only [programRename]
  have hc' := renameInto hc j Delta hj
  have hb' := renameInto hb j Delta hj
  have hn' := renameInto hn j Delta hj
  simp only [programRename] at hc' hb'
  change Nonempty (Derivation body Delta (((equal c z).relabel j).not)) at hn'
  simp only [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel,zRelabel] at hn'
  exact branchValue control a b (out.relabel j) (c.relabel j) av (out.relabel j)
    (fun i => (xs i).relabel j) hc' ha hb'
    (InternalControlGraphProof.conditionalAtNonzero (c.relabel j) av (out.relabel j) hn')
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnSupportProof
