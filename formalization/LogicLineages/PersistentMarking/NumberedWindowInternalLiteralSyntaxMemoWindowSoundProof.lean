module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowRowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenQueryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (valueUnique programRename equalEqn projectionValue successorValue headTransport zeroSuccessorCases)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim zeroBranchElim)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeReject)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization (normalize)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowStepTargets (intrinsicQuery)
open NumberedWindowInternalAuxWindowOpenTargets
open NumberedWindowInternalAuxWindowOpenQueryProof (exact_OpenIntrinsicQuery)
open NumberedWindowInternalStrictAuxWindowThinTableProof (sameContext)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxUpdate)
open NumberedWindowInternalLiteralSyntaxMemoWindow
open NumberedWindowInternalLiteralSyntaxMemoWindowRowProof (D zeroRow exact_OpenContextWindowRow)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem stepFacts (base : Program 2) (T V : Program 1) (key old ctx result : OTerm α)
    (held : D B Γ (contextStep (update base T V) (suc result) key old ctx)) :
    D B Γ (unary V (suc z) (suc key) ⊓ contextStep (strictAuxUpdate base T) (suc result) key old ctx) := by
  let xs : Fin 4 → OTerm α := ![key,old,ctx,z]
  let C := syntaxAtKey V
  let P := programGraph C (suc z) xs
  let G := unary V (suc z) (suc key) ⊓ contextStep (strictAuxUpdate base T) (suc result) key old ctx
  obtain ⟨h⟩ := held
  have yes : D B (P :: Γ) G := by
    have ok : D B (P :: Γ) P := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have proceed := successorBranchElim (normalize C) (constantZero 4) (strictAuxUpdate base T)
      (suc result) z xs (normalizeAccept C xs ok) ⟨addHyp h _⟩
    have actualKey : D B (P :: Γ) (programGraph currentKey (suc key) xs) :=
      unaryGraph .succ (.projection 0) (suc key) key xs (successorValue ![key]) (projectionValue 0 xs)
    have observed : D B (P :: Γ) (unary V (suc z) (suc key)) := by
      apply compositionRecover V (fun _ : Fin 1 => currentKey) (suc z) xs ![suc key] ok
      intro i
      obtain rfl := Fin.eq_zero i
      exact actualKey
    obtain ⟨s⟩ := observed
    obtain ⟨u⟩ := proceed
    exact ⟨Derivation.conjunctionIntroduction s u⟩
  have no : D B (P.not :: Γ) G := by
    have nope : D B (P.not :: Γ) P.not := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have bad := zeroBranchElim (normalize C) (constantZero 4) (strictAuxUpdate base T)
      (suc result) xs (normalizeReject C xs nope) ⟨addHyp h _⟩
    obtain ⟨err⟩ := valueUnique (constantZero 4) (suc result) z xs bad (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply err)⟩
  obtain ⟨s⟩ := yes
  obtain ⟨t⟩ := no
  exact ⟨disjunctionElimination (excludedMiddle P)
    (Derivation.implicationIntroduction s) (Derivation.implicationIntroduction t)⟩

theorem windowRawTransport (W : Program 3) (ctx ty raw raw' : OTerm α)
    (e : D B Γ (eqn raw raw')) (held : D B Γ (windowGraph W ctx ty raw)) :
    D B Γ (windowGraph W ctx ty raw') := by
  unfold windowGraph programGraph at held ⊢
  apply graphInputTransport B α 3 Γ (OrdinaryArithmetic.graphFormula W)
    (suc z) ![ctx,ty,raw] ![ctx,ty,raw'] _ held
  intro i
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.cases ?_ (fun x => Fin.elim0 x) l) k) i
  · change D B Γ (equal ctx ctx); rw [equalEqn]; exact ⟨refl _⟩
  · change D B Γ (equal ty ty); rw [equalEqn]; exact ⟨refl _⟩
  · change D B Γ (equal raw raw'); rw [equalEqn]; exact e

theorem windowRename {β : Type} (W : Program 3) (ctx ty raw : OTerm α) (j : α → β) :
    (windowGraph W ctx ty raw).relabel j = windowGraph W (ctx.relabel j) (ty.relabel j) (raw.relabel j) := by
  simp only [windowGraph,programRename,
    NumberedWindowInternalSparseFieldParserOpenSyntaxProof.tripleInputsRename,
    ID1Completion.InternalTagArithmeticSyntaxProof.sucRelabel,
    ID1Completion.InternalTagArithmeticSyntaxProof.zRelabel]

theorem zeroWindow (R : Program 4) (ctx ty : OTerm α)
    (held : D B Γ (windowGraph (intrinsicQuery (selectedIntrinsic R)) ctx ty z)) :
    D B Γ (⊥ : Formula α) := by
  have h := (exact_OpenIntrinsicQuery (selectedIntrinsic R) B α Γ ctx ty z).mp held
  have atZero := (sameContext R (suc ty) ctx z).mp h
  obtain ⟨bad⟩ := valueUnique (scratchRow (constantZero 2) R) (suc ty) z ![z,ctx,z]
    atZero (zeroRow R ctx)
  exact ⟨sucNeZeroApply bad⟩

/-- Positive original packed window reports directly entail the actual
raw syntax graph on the same raw key. No typing reflection is used;
the physical successor row contains the actual syntax program. -/
theorem exact_OpenSyntaxFromMemoWindow (base : Program 2) (T V : Program 1) (ctx ty raw : OTerm α)
    (held : D B Γ (windowGraph (window base T V) ctx ty raw)) :
    D B Γ (unary V (suc z) raw) := by
  let W := window base T V
  let R := update base T V
  apply zeroSuccessorCases Γ raw (unary V (suc z) raw)
  · let Δ := eqn raw z :: Γ
    obtain ⟨p⟩ := held
    have no : D B Δ (windowGraph W ctx ty z) :=
      windowRawTransport W ctx ty raw z ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp p _⟩
    exact (zeroWindow R ctx ty no).map Derivation.explosion
  · intro β j Δ k keep eq
    let c := ctx.relabel j
    let t := ty.relabel j
    let q := raw.relabel j
    let goal := (unary V (suc z) raw).relabel j
    have now := renameInto held j Δ keep
    rw [windowRename] at now
    have node := windowRawTransport W c t q (suc k) eq now
    apply exact_OpenContextWindowRow R c k t goal node
    intro γ l Ω old stay _ last
    obtain ⟨both⟩ := stepFacts base T V (k.relabel l) old (c.relabel l) (t.relabel l) last
    have source := renameInto eq l Ω stay
    rw [eqnRelabel,ID1Completion.InternalTagArithmeticSyntaxProof.sucRelabel] at source
    obtain ⟨e⟩ := source
    have h := headTransport V (suc z) (suc (k.relabel l)) (q.relabel l) Fin.elim0
      ⟨symm e⟩ ⟨Derivation.conjunctionLeft both⟩
    change D B Ω (((unary V (suc z) raw).relabel j).relabel l)
    rw [unaryRename,ID1Completion.InternalTagArithmeticSyntaxProof.sucRelabel,
      ID1Completion.InternalTagArithmeticSyntaxProof.zRelabel,unaryRename,
      ID1Completion.InternalTagArithmeticSyntaxProof.sucRelabel,
      ID1Completion.InternalTagArithmeticSyntaxProof.zRelabel]
    have one : Fin.cons (q.relabel l) Fin.elim0 = (![q.relabel l] : Fin 1 → OTerm γ) := by
      funext i
      obtain rfl := Fin.eq_zero i
      rfl
    rw [one] at h
    exact h

#print axioms exact_OpenSyntaxFromMemoWindow
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof
