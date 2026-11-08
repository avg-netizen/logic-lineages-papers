module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchGraphSupportProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalObjectFiberSourceDispatch InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalGraphCompositionFunctionalityProof InternalControlGraphSupportProof
open InternalPositiveUnfoldingSupportProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSupportProof InternalCanonicalFixedWindowVertexDispatchSupportProof
open InternalBetaTotalityProof
open InternalTagArithmeticSyntaxProof (z suc emb bindEmbedding liftBind varBind)
open InternalRawListRecursionSyntaxProof InternalComputabilityApplicationSyntaxProof
open InternalDerivationRenamingSyntaxProof SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

theorem leftTestAccept {n : Nat} (i : Fin n) (k : Nat) (xs : Fin n → OTerm α)
    (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral k) (xs i)))) :
    Nonempty (Derivation body Delta (programGraph
      (InternalApplicationStepPeel.same (leftOf (.projection i))
        (InternalCanonicalFixedWindowVertexDispatch.constant n k)) (suc z) xs)) :=
  sameAccept _ _ (numeral k) xs
    (unaryValue InternalUnpair.left (.projection i) (numeral k) (xs i) xs hl (projectionValue i xs))
    (constantValue n k xs)

theorem compositionDispatch {m n : Nat} (test old : Program m) (p : Program n)
    (gs : Fin n → Program m) (out : OTerm α) (xs : Fin m → OTerm α) (ys : Fin n → OTerm α)
    (ht : Nonempty (Derivation body Delta (programGraph test (suc z) xs)))
    (hg : ∀ i, Nonempty (Derivation body Delta (programGraph (gs i) (ys i) xs))) :
    Nonempty (Derivation body Delta
      ((programGraph (InternalAcceptance.branch test old (.composition p gs)) out xs).iff
        (programGraph p out ys))) := by
  let a := programGraph (InternalAcceptance.branch test old (.composition p gs)) out xs
  let b := programGraph p out ys
  obtain ⟨ht⟩ := ht
  have hga (i : Fin n) := (hg i).map (fun d => addHyp d a)
  have hgb (i : Fin n) := (hg i).map (fun d => addHyp d b)
  obtain ⟨hf⟩ := compositionRecover p gs out xs ys
    (successorBranchElim test old (.composition p gs) out z xs
      ⟨addHyp ht a⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩) hga
  obtain ⟨hb⟩ := successorBranchIntro test old (.composition p gs) out z xs
    ⟨addHyp ht b⟩ (compositionValue p gs out xs ys
      ⟨Derivation.hypothesis List.mem_cons_self⟩ hgb)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem positiveInputs (xs : Fin 4 → OTerm α) (source target : OTerm α)
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right source (xs 1) ⊓ graph1 InternalUnpair.right target (xs 2)))) :
    ∀ i : Fin 3, Nonempty (Derivation body Delta
      (programGraph ((![rightOf (.projection 1),rightOf (.projection 2),.projection 3] : Fin 3 → Program 4) i)
        ((Fin.cons source (Fin.cons target (Fin.cons (xs 3) Fin.elim0)) : Fin 3 → OTerm α) i) xs)) := by
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.elim0 l) k) j) i
  · exact unaryValue InternalUnpair.right (.projection 1) source (xs 1) xs (andLeft hr) (projectionValue 1 xs)
  · exact unaryValue InternalUnpair.right (.projection 2) target (xs 2) xs (andRight hr) (projectionValue 2 xs)
  · exact projectionValue 3 xs

theorem typedInputs (xs : Fin 3 → OTerm α) (payload : OTerm α)
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload (xs 2)))) :
    ∀ i : Fin 2, Nonempty (Derivation body Delta
      (programGraph ((![rightOf (.projection 2),.projection 1] : Fin 2 → Program 3) i)
        ((Fin.cons payload (Fin.cons (xs 1) Fin.elim0) : Fin 2 → OTerm α) i) xs)) := by
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
  · exact unaryValue InternalUnpair.right (.projection 2) payload (xs 2) xs hr (projectionValue 2 xs)
  · exact projectionValue 1 xs

theorem resultInputs (xs : Fin 5 → OTerm α) (function argument : OTerm α)
    (hf : Nonempty (Derivation body Delta (graph1 InternalUnpair.right function (xs 3))))
    (ha : Nonempty (Derivation body Delta (graph1 InternalUnpair.right argument (xs 4)))) :
    ∀ i : Fin 4, Nonempty (Derivation body Delta
      (programGraph ((![.projection 1,.projection 2,rightOf (.projection 3),rightOf (.projection 4)] : Fin 4 → Program 5) i)
        ((Fin.cons (xs 1) (Fin.cons (xs 2) (Fin.cons function (Fin.cons argument Fin.elim0))) : Fin 4 → OTerm α) i) xs)) := by
  intro i
  exact Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 2 xs)
    (Fin.cases (unaryValue InternalUnpair.right (.projection 3) function (xs 3) xs hf (projectionValue 3 xs))
      (Fin.cases (unaryValue InternalUnpair.right (.projection 4) argument (xs 4) xs ha (projectionValue 4 xs))
        (fun j => Fin.elim0 j)))) i

theorem resultTestAccept (window : Nat) (Gamma : List Ty) (data : Data)
    (context domain codomain functionObject argumentObject function argument : OTerm α)
    (h : Nonempty (Derivation body Delta (resultPremises window Gamma data context domain codomain
      functionObject argumentObject function argument))) :
    Nonempty (Derivation body Delta (programGraph (resultActivation window Gamma data) (suc z)
      (resultArguments context domain codomain functionObject argumentObject))) := by
  let xs := resultArguments context domain codomain functionObject argumentObject
  apply conjunctionAccept _ _ xs (leftTestAccept 3 (Encodable.encode Gamma) xs (andLeft (andLeft h)))
  apply conjunctionAccept _ _ xs (leftTestAccept 4 (Encodable.encode Gamma) xs (andLeft (andLeft (andRight h))))
  apply compositionValue (InternalCanonicalFixedWindowVertexDispatch.activation window data)
    ![.projection 0,.projection 1,.projection 2,rightOf (.projection 4),rightOf (.projection 3)]
    (suc z) xs (InternalApplicationPathMap.vertexArguments context domain codomain argument function)
    (andRight (andRight h))
  intro i
  exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
    (Fin.cases (projectionValue 2 xs)
      (Fin.cases (unaryValue InternalUnpair.right (.projection 4) argument (xs 4) xs
        (andRight (andLeft (andRight h))) (projectionValue 4 xs))
        (Fin.cases (unaryValue InternalUnpair.right (.projection 3) function (xs 3) xs
          (andRight (andLeft h)) (projectionValue 3 xs)) (fun j => Fin.elim0 j))))) i

/-- Existential intermediate is the actual program output, paired with the supplied out. -/
def paired {n : Nat} (k : Nat) (p : Program n) (out : OTerm α) (xs : Fin n → OTerm α) : Formula α :=
  existsOne (programGraph p (.var (.inr (0 : Fin 1))) (fun i => (xs i).relabel Sum.inl) ⊓
    graph2 InternalPairing.pairing (out.relabel Sum.inl) (numeral k) (.var (.inr 0)))

theorem pairedApplicationEq (Gamma : List Ty) (data : Data)
    (out domain codomain function argument : OTerm α) :
    pairedApplicationGraph Gamma data out domain codomain function argument =
      paired (Encodable.encode Gamma) (InternalCanonicalQuotientEdgeApplicationLift.actualJ data) out
        (Fin.cons domain (Fin.cons codomain (Fin.cons function (Fin.cons argument Fin.elim0)))) := by
  simp only [pairedApplicationGraph,paired,InternalCanonicalQuotientEdgeApplicationLift.applicationGraph,
    graph4,consTermRename,emptyRename]

@[simp] theorem pairedRename {n : Nat} {β : Type} (k : Nat) (p : Program n)
    (out : OTerm α) (xs : Fin n → OTerm α) (j : α → β) :
    (paired k p out xs).relabel j = paired k p (out.relabel j) (fun i => (xs i).relabel j) := by
  have hm : (Sum.map j (id : Fin 1 → Fin 1)) ∘ Sum.inl = Sum.inl ∘ j := rfl
  have hv : ((.var (.inr (0 : Fin 1)) : OTerm (α ⊕ Fin 1)).relabel (Sum.map j id)) =
      (.var (.inr (0 : Fin 1)) : OTerm (β ⊕ Fin 1)) := rfl
  simp only [paired,existsRename,conjunctionRename,graph2,programRename,
    consTermRename,emptyRename,Term.relabel_relabel,hm,hv,GuardedSourceSyntaxProof.numeralRename]

theorem pairedInstantiate {n : Nat} (k : Nat) (p : Program n)
    (out : OTerm α) (xs : Fin n → OTerm α) (value : OTerm α) :
    instantiate (programGraph p (.var (.inr (0 : Fin 1))) (fun i => (xs i).relabel Sum.inl) ⊓
      graph2 InternalPairing.pairing (out.relabel Sum.inl) (numeral k) (.var (.inr 0))) (emb value) =
      programGraph p value xs ⊓ graph2 InternalPairing.pairing out (numeral k) value := by
  rw [instantiate,bindEmbedding]
  change (programGraph p _ _).subst _ ⊓ (graph2 InternalPairing.pairing _ _ _).subst _ = _
  simp only [graph2,InternalRawListRecursionSyntaxProof.programSubst,consTermSubst,emptySubst,
    liftBind,varBind,InternalComputabilityApplicationSyntaxProof.numeralSubst]

theorem pairedIntro {n : Nat} (k : Nat) (p : Program n) (out : OTerm α)
    (xs : Fin n → OTerm α) (value : OTerm α)
    (hp : Nonempty (Derivation body Delta (programGraph p value xs)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral k) value))) :
    Nonempty (Derivation body Delta (paired k p out xs)) := by
  obtain ⟨h⟩ := andIntro hp hr
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb value)
  rw [pairedInstantiate]
  exact h

theorem pairedCases {n : Nat} (k : Nat) (p : Program n) (out : OTerm α)
    (xs : Fin n → OTerm α) (psi : Formula α)
    (hr : Nonempty (Derivation body Delta (paired k p out xs)))
    (h : ∀ (β : Type) (j : α → β) (Theta : List (Formula β)) (value : OTerm β),
      (∀ r ∈ Delta, r.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (programGraph p value (fun i => (xs i).relabel j))) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (out.relabel j) (numeral k) value)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨hr⟩ := hr
  let mat := programGraph p (.var (.inr (0 : Fin 1))) (fun i => (xs i).relabel Sum.inl) ⊓
    graph2 InternalPairing.pairing (out.relabel Sum.inl) (numeral k) (.var (.inr 0))
  have hm : Derivation body (mat :: Delta.map weaken) mat := Derivation.hypothesis List.mem_cons_self
  obtain ⟨hk⟩ := h (α ⊕ Fin 1) Sum.inl (mat :: Delta.map weaken) (.var (.inr 0))
    (by intro r hr; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,hr,rfl⟩))
    ⟨Derivation.conjunctionLeft hm⟩ ⟨Derivation.conjunctionRight hm⟩
  exact ⟨Derivation.existentialElimination hr hk⟩

theorem pairCompositionRecover {m n : Nat} (k : Nat) (p : Program n)
    (gs : Fin n → Program m) (out : OTerm α) (xs : Fin m → OTerm α) (ys : Fin n → OTerm α)
    (hg : ∀ i, Nonempty (Derivation body Delta (programGraph (gs i) (ys i) xs)))
    (h : Nonempty (Derivation body Delta (programGraph
      (pairOf (InternalCanonicalFixedWindowVertexDispatch.constant m k) (.composition p gs)) out xs))) :
    Nonempty (Derivation body Delta (paired k p out ys)) := by
  apply programCases p ys _
  intro β j Theta v hj hv
  rw [pairedRename]
  have h' := renameInto h j Theta hj
  simp only [programRename] at h'
  have hg' (i : Fin n) := renameInto (hg i) j Theta hj
  simp only [programRename] at hg'
  exact pairedIntro k p (out.relabel j) (fun i => (ys i).relabel j) v hv
    (binaryRecover InternalPairing.pairing (InternalCanonicalFixedWindowVertexDispatch.constant m k)
      (.composition p gs) (out.relabel j) (numeral k) v (fun i => (xs i).relabel j) h'
      (constantValue m k _) (compositionValue p gs v _ _ hv hg'))

theorem pairCompositionAccept {m n : Nat} (k : Nat) (p : Program n)
    (gs : Fin n → Program m) (out : OTerm α) (xs : Fin m → OTerm α) (ys : Fin n → OTerm α)
    (hg : ∀ i, Nonempty (Derivation body Delta (programGraph (gs i) (ys i) xs)))
    (h : Nonempty (Derivation body Delta (paired k p out ys))) :
    Nonempty (Derivation body Delta (programGraph
      (pairOf (InternalCanonicalFixedWindowVertexDispatch.constant m k) (.composition p gs)) out xs)) := by
  apply pairedCases k p out ys _ h
  intro β j Theta v hj hv hp
  simp only [programRename]
  have hg' (i : Fin n) := renameInto (hg i) j Theta hj
  simp only [programRename] at hg'
  exact binaryValue InternalPairing.pairing (InternalCanonicalFixedWindowVertexDispatch.constant m k)
    (.composition p gs) (out.relabel j) (numeral k) v (fun i => (xs i).relabel j) hp
    (constantValue m k _) (compositionValue p gs v _ _ hv hg')

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchGraphSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchGraphSupportProof
