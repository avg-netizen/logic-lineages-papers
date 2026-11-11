module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationWorkProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalGraphCompositionEqualityProof
open InternalSourceInversionSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb eqn eqnRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem binaryRightTransport (p : Program 2) (out first old new : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (eqn old new)))
    (hp : Nonempty (Derivation body Gamma (graph2 p out first old))) :
    Nonempty (Derivation body Gamma (graph2 p out first new)) := by
  apply graphInputTransport body alpha 2 Gamma (OrdinaryArithmetic.graphFormula p) out
    (Fin.cons first (Fin.cons old Fin.elim0)) (Fin.cons first (Fin.cons new Fin.elim0)) _ hp
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i
  · rw [onEquality]; exact ⟨refl first⟩
  · rw [onEquality]; exact he

theorem workRunIntro (s t m : Program 2) (out count workCode state : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StateGraph state (numeral 1) workCode)))
    (hr : Nonempty (Derivation body Gamma (graph2 (iterate s t m) out count state))) :
    Nonempty (Derivation body Gamma (WorkRun s t m out count workCode)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 1 Gamma
    (runMatrix s t m out count workCode) (fun i => emb ((![state] : Fin 1 → OTerm alpha) i))
  rw [runMatrixWitness]
  exact andIntro hs hr

theorem workRunCases (s t m : Program 2) (out count workCode : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Gamma (WorkRun s t m out count workCode)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)) (state : OTerm beta),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (StateGraph state (numeral 1) (workCode.relabel j))) →
      Nonempty (Derivation body Delta
        (graph2 (iterate s t m) (out.relabel j) (count.relabel j) state)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 1 Gamma
    (runMatrix s t m out count workCode) psi h
  apply step (alpha ⊕ Fin 1) Sum.inl
    (runMatrix s t m out count workCode :: Gamma.map (fun p => p.relabel Sum.inl)) (.var (.inr 0))
  · intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  · exact ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩

theorem workRunAt (s t m : Program 2) (out count workCode state : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StateGraph state (numeral 1) workCode)))
    (hr : Nonempty (Derivation body Gamma (WorkRun s t m out count workCode))) :
    Nonempty (Derivation body Gamma (graph2 (iterate s t m) out count state)) := by
  apply workRunCases s t m out count workCode _ hr
  intro beta j Delta actual hj ha hi
  rw [graph2Rename]
  have hs' := renameInto hs j Delta hj
  simp only [StateGraph,graph2Rename,oneRename] at hs'
  have he := valueUnique InternalPairing.pairing actual (state.relabel j)
    (Fin.cons (numeral 1) (Fin.cons (workCode.relabel j) Fin.elim0)) ha hs'
  exact binaryRightTransport (iterate s t m) (out.relabel j) (count.relabel j)
    actual (state.relabel j) he hi

theorem terminatedIntro (s t m : Program 2) (count workCode out : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma (WorkRun s t m out count workCode)))
    (ht : Nonempty (Derivation body Gamma (Terminal out))) :
    Nonempty (Derivation body Gamma (TerminatedWork s t m count workCode)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 1 Gamma
    (terminatedMatrix s t m count workCode) (fun i => emb ((![out] : Fin 1 → OTerm alpha) i))
  rw [terminatedMatrixWitness]
  exact andIntro hr ht

theorem terminatedCases (s t m : Program 2) (count workCode : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Gamma (TerminatedWork s t m count workCode)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)) (out : OTerm beta),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (WorkRun s t m out (count.relabel j) (workCode.relabel j))) →
      Nonempty (Derivation body Delta (Terminal out)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 1 Gamma
    (terminatedMatrix s t m count workCode) psi h
  apply step (alpha ⊕ Fin 1) Sum.inl
    (terminatedMatrix s t m count workCode :: Gamma.map (fun p => p.relabel Sum.inl)) (.var (.inr 0))
  · intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  · exact ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩

theorem acceptedIntro (s t m : Program 2) (workCode count : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph count workCode)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork s t m count workCode))) :
    Nonempty (Derivation body Gamma (WorkAccepted s t m workCode)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 1 Gamma
    (acceptedMatrix s t m workCode) (fun i => emb ((![count] : Fin 1 → OTerm alpha) i))
  rw [acceptedMatrixWitness]
  exact andIntro hf hs

theorem acceptedCases (s t m : Program 2) (workCode : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Gamma (WorkAccepted s t m workCode)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)) (count : OTerm beta),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (WorkFuelGraph count (workCode.relabel j))) →
      Nonempty (Derivation body Delta (SuccessfulWork s t m count (workCode.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 1 Gamma
    (acceptedMatrix s t m workCode) psi h
  apply step (alpha ⊕ Fin 1) Sum.inl
    (acceptedMatrix s t m workCode :: Gamma.map (fun p => p.relabel Sum.inl)) (.var (.inr 0))
  · intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  · exact ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩

theorem workRunCountTransport (s t m : Program 2) (out count other workCode : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (eqn count other)))
    (hr : Nonempty (Derivation body Gamma (WorkRun s t m out count workCode))) :
    Nonempty (Derivation body Gamma (WorkRun s t m out other workCode)) := by
  apply workRunCases s t m out count workCode _ hr
  intro beta j Delta state hj hs hi
  rw [workRunRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact workRunIntro s t m (out.relabel j) (other.relabel j) (workCode.relabel j) state hs
    (headTransport (iterate s t m) (out.relabel j) (count.relabel j) (other.relabel j)
      (Fin.cons state Fin.elim0) he' hi)

theorem workRunWorkTransport (s t m : Program 2) (out count workCode other : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (eqn workCode other)))
    (hr : Nonempty (Derivation body Gamma (WorkRun s t m out count workCode))) :
    Nonempty (Derivation body Gamma (WorkRun s t m out count other)) := by
  apply workRunCases s t m out count workCode _ hr
  intro beta j Delta state hj hs hi
  rw [workRunRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact workRunIntro s t m (out.relabel j) (count.relabel j) (other.relabel j) state
    (binaryRightTransport InternalPairing.pairing state (numeral 1)
      (workCode.relabel j) (other.relabel j) he' hs) hi

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationWorkProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationWorkProof
