module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableEraseLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSpecSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalRecursionClosureSyntaxProof
open InternalRawListRecursionSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb bindEmbedding varBind liftBind eqnRelabel zRelabel sucRelabel)
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof
open InternalPositiveUnfoldingSupportProof
open InternalDerivationRenamingSyntaxProof (existsRename)
open InternalBetaTotalityProof (disjunctionElimination)
open SourceComputabilityFormulaSupportProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Only a proof-side name for the frozen existential predecessor conjunct. -/
def PreviousResult (out i : OTerm alpha) : Formula alpha := existsOne
  (graph1 InternalEqualityTest.predecessor (.var (.inr 0)) (i.relabel Sum.inl) ⊓
    graph1 variableConstructor (out.relabel Sum.inl) (.var (.inr 0)))

/-- Keep both Programs symbolic during binder normalization. -/
theorem chainExistsRename {beta : Type} (p q : Program 1)
    (out i : OTerm alpha) (j : alpha → beta) :
    (existsOne (graph1 p (.var (.inr 0)) (i.relabel Sum.inl) ⊓
      graph1 q (out.relabel Sum.inl) (.var (.inr 0)))).relabel j =
    existsOne (graph1 p (.var (.inr 0)) ((i.relabel j).relabel Sum.inl) ⊓
      graph1 q ((out.relabel j).relabel Sum.inl) (.var (.inr 0))) := by
  rw [existsRename]
  congr 1
  simp only [conjunctionRename,graph1Rename,Term.relabel_relabel,Term.relabel]
  rfl

@[simp] theorem previousRename {beta : Type} (out i : OTerm alpha) (j : alpha → beta) :
    (PreviousResult out i).relabel j = PreviousResult (out.relabel j) (i.relabel j) :=
  chainExistsRename InternalEqualityTest.predecessor variableConstructor out i j

theorem previousInstantiate (out i previous : OTerm alpha) :
    instantiate (graph1 InternalEqualityTest.predecessor (.var (.inr 0)) (i.relabel Sum.inl) ⊓
      graph1 variableConstructor (out.relabel Sum.inl) (.var (.inr 0))) (emb previous) =
      graph1 InternalEqualityTest.predecessor previous i ⊓ graph1 variableConstructor out previous := by
  rw [instantiate,bindEmbedding,conjunctionSubst]
  simp only [graph1,programSubst,consTermSubst,emptySubst,varBind,liftBind]

theorem previousIntro (out i previous : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 InternalEqualityTest.predecessor previous i)))
    (hv : Nonempty (Derivation body Delta (graph1 variableConstructor out previous))) :
    Nonempty (Derivation body Delta (PreviousResult out i)) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hv⟩ := hv
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb previous)
  rw [previousInstantiate]
  exact Derivation.conjunctionIntroduction hp hv

theorem previousCases (out i : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (PreviousResult out i)))
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (previous : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph1 InternalEqualityTest.predecessor previous (i.relabel j))) →
      Nonempty (Derivation body Theta (graph1 variableConstructor (out.relabel j) previous)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨h⟩ := h
  let P := graph1 InternalEqualityTest.predecessor (.var (.inr (0 : Fin 1))) (i.relabel Sum.inl) ⊓
    graph1 variableConstructor (out.relabel Sum.inl) (.var (.inr 0))
  let Theta := P :: Delta.map weaken
  obtain ⟨d⟩ := k (alpha ⊕ Fin 1) Sum.inl Theta (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.existentialElimination h d⟩

@[simp] theorem variableSpecRename {beta : Type} (mode : Mode)
    (out d k i : OTerm alpha) (j : alpha → beta) :
    (VariableSpec mode out d k i).relabel j =
      VariableSpec mode (out.relabel j) (d.relabel j) (k.relabel j) (i.relabel j) := by
  cases mode with
  | rank => simp only [VariableSpec,equalEqn,eqnRelabel,numeral,sucRelabel,zRelabel]
  | shift =>
    change (((InternalLessThan.strictLess i k).relabel j ⊓
      (graph1 variableConstructor out i).relabel j) ⊔
      (((InternalLessThan.strictLess i k).relabel j).not ⊓
        (graph1 variableConstructor out (suc i)).relabel j)) = _
    simp only [VariableSpec,InternalLessThan.strictLess,orderRename,graph1Rename,sucRelabel]
  | erase =>
    change (((InternalLessThan.strictLess i k).relabel j ⊓
      (graph1 variableConstructor out i).relabel j) ⊔
      (((equal i k).relabel j ⊓ (graph1 bottomConstructor out d).relabel j) ⊔
        ((InternalLessThan.strictLess k i).relabel j ⊓ (PreviousResult out i).relabel j))) = _
    rw [previousRename]
    simp only [VariableSpec,InternalLessThan.strictLess,orderRename,graph1Rename,equalEqn,eqnRelabel]
    rfl

theorem orCases {p q psi : Formula alpha}
    (h : Nonempty (Derivation body Delta (p ⊔ q)))
    (hp : Nonempty (Derivation body (p :: Delta) psi))
    (hq : Nonempty (Derivation body (q :: Delta) psi)) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := hp
  obtain ⟨hq⟩ := hq
  exact ⟨disjunctionElimination h (Derivation.implicationIntroduction hp)
    (Derivation.implicationIntroduction hq)⟩

/-- Every erasure branch is reached by the existing internal arithmetic
trichotomy, including both strict comparisons. -/
theorem indexCases (i k : OTerm alpha) (psi : Formula alpha)
    (hlt : Nonempty (Derivation body (InternalLessThan.strictLess i k :: Delta) psi))
    (heq : Nonempty (Derivation body (equal i k :: Delta) psi))
    (hgt : Nonempty (Derivation body (InternalLessThan.strictLess k i :: Delta) psi)) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨hc⟩ := actualOriginalComparison body alpha i k
  have hc' : Nonempty (Derivation body Delta
      (InternalLessThan.strictLess i k ⊔ (equal i k ⊔ InternalLessThan.strictLess k i))) := by
    simpa only [InternalLessThan.strictLess,equalEqn] using
      (Nonempty.intro (compareView (weakenClosed hc Delta)))
  obtain ⟨hc'⟩ := hc'
  obtain ⟨hlt⟩ := hlt
  obtain ⟨heq⟩ := heq
  obtain ⟨hgt⟩ := hgt
  have hr : Derivation body Delta ((equal i k ⊔ InternalLessThan.strictLess k i).imp psi) :=
    Derivation.implicationIntroduction (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (InternalBetaTotalityProof.addHyp (Derivation.implicationIntroduction heq) _)
      (InternalBetaTotalityProof.addHyp (Derivation.implicationIntroduction hgt) _))
  exact ⟨disjunctionElimination hc' (Derivation.implicationIntroduction hlt) hr⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSpecSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSpecSyntaxProof
