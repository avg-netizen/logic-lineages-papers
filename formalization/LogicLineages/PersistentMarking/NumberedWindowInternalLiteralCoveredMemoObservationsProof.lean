module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoRowSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoObservationsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport zeroSuccessorCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalLiteralSyntaxMemoWindowRowProof (D exact_OpenContextWindowRow)
open NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof (windowRename windowRawTransport zeroWindow)
open NumberedWindowInternalLiteralCoveredMemo
open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport coverStepFacts)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def observations {α : Type} (C : Program 3) (s : Settings) (V : Program 1)
    (ctx raw : OTerm α) : Formula α := coverageReport C s ctx raw ⊓ unary V (suc z) raw

theorem observationsRename {β : Type} (C : Program 3) (s : Settings) (V : Program 1)
    (ctx raw : OTerm α) (j : α → β) :
    (observations C s V ctx raw).relabel j = observations C s V (ctx.relabel j) (raw.relabel j) := by
  unfold observations
  rw [conjunctionRename,unaryRename,sucRelabel,zRelabel]
  change (windowGraph (conjunction contextPresent (ownSeed C s)) ctx z raw).relabel j ⊓
    unary V (suc z) (raw.relabel j) = _
  rw [windowRename,zRelabel]
  rfl

/-- The original syntax and both least-domain tests are recovered from
an actual positive bounded memo query, at any raw open key. -/
theorem exact_OpenCoveredMemoObservations (C : Program 3) (s : Settings) (base : Program 2) (T V : Program 1)
    (ctx ty raw : OTerm α) (held : D B Γ (windowGraph (coveredMemoWindow C s base T V) ctx ty raw)) :
    D B Γ (observations C s V ctx raw) := by
  let R := coveredUpdate C s base T V
  let W := coveredMemoWindow C s base T V
  let G := conjunction contextPresent (ownSeed C s)
  apply zeroSuccessorCases Γ raw (observations C s V ctx raw)
  · let Δ := eqn raw z :: Γ
    obtain ⟨d⟩ := held
    have no : D B Δ (windowGraph W ctx ty z) :=
      windowRawTransport W ctx ty raw z ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp d _⟩
    exact (zeroWindow R ctx ty no).map Derivation.explosion
  · intro β j Δ key keep equal
    rw [observationsRename]
    let ctx' := ctx.relabel j
    let ty' := ty.relabel j
    let q := raw.relabel j
    have moved := renameInto held j Δ keep
    rw [windowRename] at moved
    have hit := windowRawTransport W ctx' ty' q (suc key) equal moved
    apply exact_OpenContextWindowRow R ctx' key ty' _ hit
    intro γ l Ω old stay _ last
    rw [observationsRename]
    obtain ⟨row⟩ := coverStepFacts C s base T V (key.relabel l) old (ctx'.relabel l) (ty'.relabel l) last
    have e := renameInto equal l Ω stay
    rw [eqnRelabel,sucRelabel] at e
    obtain ⟨eq⟩ := e
    have cv : D B Ω (coverageReport C s (ctx'.relabel l) (q.relabel l)) :=
      windowRawTransport G (ctx'.relabel l) z (suc (key.relabel l)) (q.relabel l)
        ⟨symm eq⟩ ⟨Derivation.conjunctionLeft row⟩
    have sv : D B Ω (unary V (suc z) (q.relabel l)) := by
      have exactGraph := headTransport V (suc z) (suc (key.relabel l)) (q.relabel l) Fin.elim0
        ⟨symm eq⟩ ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight row)⟩
      have one : Fin.cons (q.relabel l) Fin.elim0 = (![q.relabel l] : Fin 1 → OTerm γ) := by
        funext i
        obtain rfl := Fin.eq_zero i
        rfl
      simpa only [unary,one] using exactGraph
    obtain ⟨a⟩ := cv
    obtain ⟨b⟩ := sv
    exact ⟨Derivation.conjunctionIntroduction a b⟩

#print axioms exact_OpenCoveredMemoObservations
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoObservationsProof
