module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalStateSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalPushSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalHereditaryValidityInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb sucSubst zSubst)
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open SourceComputabilityFormulaSupportProof (numeral)

/-- Ordinary witnesses use the existing arithmetic embedding. -/
theorem witnessEmbedding {alpha : Type} {k : Nat} (ys : Fin k → OTerm alpha) :
    (Sum.elim Term.var (fun i => emb (ys i))) =
      (fun a => emb (Sum.elim Term.var ys a)) := by
  funext a
  cases a <;> rfl

theorem stateFrameSubst {alpha beta : Type}
    (state work frame raw parameter rest : OTerm alpha) (ts : alpha → OTerm beta) :
    (StateFrame state work frame raw parameter rest).subst (fun a => emb (ts a)) =
      StateFrame (state.subst ts) (work.subst ts) (frame.subst ts)
        (raw.subst ts) (parameter.subst ts) (rest.subst ts) := by
  simp only [StateFrame,StateGraph,WorkCons,FrameGraph,conjunctionSubst,
    graph2,programSubst,consTermSubst,emptySubst,numeral,sucSubst,zSubst]

def frameMatrix {alpha : Type} (out raw parameter rest : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  StateFrame (out.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
    (raw.relabel Sum.inl) (parameter.relabel Sum.inl) (rest.relabel Sum.inl)

theorem frameMatrixWitness {alpha : Type}
    (out raw parameter rest work frame : OTerm alpha) :
    (frameMatrix out raw parameter rest).subst
      (Sum.elim Term.var (fun i => emb (![work,frame] i))) =
      StateFrame out work frame raw parameter rest := by
  unfold frameMatrix
  rw [witnessEmbedding,stateFrameSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem pushedFrameIntro {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (out raw parameter rest work frame : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StateFrame out work frame raw parameter rest))) :
    Nonempty (Derivation body Delta (PushedFrame out raw parameter rest)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 2 Delta (frameMatrix out raw parameter rest)
    (fun i => emb (![work,frame] i))
  rw [frameMatrixWitness]
  exact h

theorem pushedFrameCases {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (out raw parameter rest : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (PushedFrame out raw parameter rest)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (work frame : OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (StateFrame (out.relabel j) work frame
        (raw.relabel j) (parameter.relabel j) (rest.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 2 Delta (frameMatrix out raw parameter rest) psi h
  apply step (alpha ⊕ Fin 2) Sum.inl
    (frameMatrix out raw parameter rest :: Delta.map (fun p => p.relabel Sum.inl))
    (.var (.inr 0)) (.var (.inr 1))
  · intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem pushedFrameSubst {alpha beta : Type}
    (out raw parameter rest : OTerm alpha) (ts : alpha → OTerm beta) :
    (PushedFrame out raw parameter rest).subst (fun a => emb (ts a)) =
      PushedFrame (out.subst ts) (raw.subst ts) (parameter.subst ts) (rest.subst ts) := by
  unfold PushedFrame InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  simp only [stateFrameSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem pushedFrameRename {alpha beta : Type}
    (out raw parameter rest : OTerm alpha) (j : alpha → beta) :
    (PushedFrame out raw parameter rest).relabel j =
      PushedFrame (out.relabel j) (raw.relabel j) (parameter.relabel j) (rest.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (PushedFrame out raw parameter rest).subst (fun a => emb (.var (j a))) = _
  rw [pushedFrameSubst]
  simp only [← termRelabelAsSubst]

def appFields {alpha : Type}
    (out fn arg parameter rest work suffix fnFrame argFrame : OTerm alpha) : Formula alpha :=
  StateGraph out (numeral 1) work ⊓
    (WorkCons work fnFrame suffix ⊓
      (FrameGraph fnFrame fn parameter ⊓
        (WorkCons suffix argFrame rest ⊓ FrameGraph argFrame arg parameter)))

def appMatrix {alpha : Type} (out fn arg parameter rest : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  appFields (out.relabel Sum.inl) (fn.relabel Sum.inl) (arg.relabel Sum.inl)
    (parameter.relabel Sum.inl) (rest.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))

theorem appFieldsSubst {alpha beta : Type}
    (out fn arg parameter rest work suffix fnFrame argFrame : OTerm alpha) (ts : alpha → OTerm beta) :
    (appFields out fn arg parameter rest work suffix fnFrame argFrame).subst (fun a => emb (ts a)) =
      appFields (out.subst ts) (fn.subst ts) (arg.subst ts) (parameter.subst ts)
        (rest.subst ts) (work.subst ts) (suffix.subst ts) (fnFrame.subst ts) (argFrame.subst ts) := by
  simp only [appFields,StateGraph,WorkCons,FrameGraph,conjunctionSubst,
    graph2,programSubst,consTermSubst,emptySubst,numeral,sucSubst,zSubst]

theorem appMatrixWitness {alpha : Type}
    (out fn arg parameter rest work suffix fnFrame argFrame : OTerm alpha) :
    (appMatrix out fn arg parameter rest).subst
      (Sum.elim Term.var (fun i => emb (![work,suffix,fnFrame,argFrame] i))) =
      appFields out fn arg parameter rest work suffix fnFrame argFrame := by
  unfold appMatrix
  rw [witnessEmbedding,appFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem pushedApplicationIntro {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (out fn arg parameter rest work suffix fnFrame argFrame : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (appFields out fn arg parameter rest work suffix fnFrame argFrame))) :
    Nonempty (Derivation body Delta (PushedApplication out fn arg parameter rest)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 4 Delta (appMatrix out fn arg parameter rest)
    (fun i => emb (![work,suffix,fnFrame,argFrame] i))
  rw [appMatrixWitness]
  exact h

theorem pushedApplicationCases {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (out fn arg parameter rest : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (PushedApplication out fn arg parameter rest)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (work suffix fnFrame argFrame : OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (appFields (out.relabel j) (fn.relabel j) (arg.relabel j)
        (parameter.relabel j) (rest.relabel j) work suffix fnFrame argFrame)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 4 Delta (appMatrix out fn arg parameter rest) psi h
  apply step (alpha ⊕ Fin 4) Sum.inl
    (appMatrix out fn arg parameter rest :: Delta.map (fun p => p.relabel Sum.inl))
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))
  · intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem pushedApplicationSubst {alpha beta : Type}
    (out fn arg parameter rest : OTerm alpha) (ts : alpha → OTerm beta) :
    (PushedApplication out fn arg parameter rest).subst (fun a => emb (ts a)) =
      PushedApplication (out.subst ts) (fn.subst ts) (arg.subst ts)
        (parameter.subst ts) (rest.subst ts) := by
  change (InternalFiniteBlocks.block (appMatrix out fn arg parameter rest)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold appMatrix
  simp only [appFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem pushedApplicationRename {alpha beta : Type}
    (out fn arg parameter rest : OTerm alpha) (j : alpha → beta) :
    (PushedApplication out fn arg parameter rest).relabel j =
      PushedApplication (out.relabel j) (fn.relabel j) (arg.relabel j)
        (parameter.relabel j) (rest.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (PushedApplication out fn arg parameter rest).subst (fun a => emb (.var (j a))) = _
  rw [pushedApplicationSubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalPushSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalPushSyntaxProof
