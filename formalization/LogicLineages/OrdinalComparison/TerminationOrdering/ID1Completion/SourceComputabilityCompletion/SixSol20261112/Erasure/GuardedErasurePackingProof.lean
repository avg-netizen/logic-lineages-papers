module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.FinalErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasurePackingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open OriginalFinalVariableCanonicalSupportProof (iffForward iffBackward)
open OriginalTransparentLambdaFinalLogicProof (iffSelf orIff)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalBetaTotalityProof (disjunctionElimination)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedErasureTargets GuardedErasureSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

/-- Auxiliary observer for the already checked generic outLeaf induction.
Both conjuncts consume the SAME original four-input vector. -/
def pairedLeaf (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf : Program 4) : Program 4 :=
  InternalAcceptance.conjunction rawLeaf (UniformCertificateCompletion.stepChecker D oldStep)

theorem certificateRecover (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf : Program 4) (s t cert parameter : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (graph4 (pairedLeaf D oldStep rawLeaf) (numeral 1) s t cert parameter))) :
    Nonempty (Derivation body Delta (Certificate D oldStep rawLeaf s t cert parameter)) := by
  simpa only [Certificate,UniformCertificateCompletion.stepAccepted,
    InternalOriginalStepGuard.one,SourceComputabilityFormulaSupportProof.numeral] using
    conjunctionRecover rawLeaf (UniformCertificateCompletion.stepChecker D oldStep)
      (Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))) h

theorem certificateAccept (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf : Program 4) (s t cert parameter : OTerm alpha)
    (h : Nonempty (Derivation body Delta (Certificate D oldStep rawLeaf s t cert parameter))) :
    Nonempty (Derivation body Delta
      (graph4 (pairedLeaf D oldStep rawLeaf) (numeral 1) s t cert parameter)) := by
  exact conjunctionAccept rawLeaf (UniformCertificateCompletion.stepChecker D oldStep)
    (Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0))))
    (andLeft h) (andRight h)

/-- The original existential binder is opened once. Every consumer receives
both facts at that ONE certificate under the actual fresh-variable context. -/
theorem withWitness (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf : Program 4) (s t parameter : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (Witness D oldStep rawLeaf s t parameter)))
    (consume : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (cert : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (Certificate D oldStep rawLeaf (s.relabel j) (t.relabel j) cert (parameter.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialElimination h
  change Derivation body (WitnessMatrix D oldStep rawLeaf s t parameter :: Delta.map weaken)
    (psi.relabel (Sum.inl : alpha → alpha ⊕ Fin 1))
  exact Classical.choice (consume (alpha ⊕ Fin 1) Sum.inl _ (.var (.inr 0))
    (fun q hq => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩)

theorem witnessToPaired (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf : Program 4) (s t parameter : OTerm alpha)
    (h : Nonempty (Derivation body Delta (Witness D oldStep rawLeaf s t parameter))) :
    Nonempty (Derivation body Delta
      (OriginalLambdaErasureSquareDichotomyDefinitions.Witness (pairedLeaf D oldStep rawLeaf) s t parameter)) := by
  apply withWitness D oldStep rawLeaf s t parameter _ h
  intro beta j Theta cert hj hc
  rw [OriginalLambdaErasureSquareDichotomySyntaxProof.witnessRename]
  exact OriginalLambdaErasureSquareDichotomySyntaxProof.witnessIntro
    (pairedLeaf D oldStep rawLeaf) (s.relabel j) (t.relabel j) (parameter.relabel j) cert
    (certificateAccept D oldStep rawLeaf (s.relabel j) (t.relabel j) cert (parameter.relabel j) hc)

theorem witnessFromPaired (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf : Program 4) (s t parameter : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (OriginalLambdaErasureSquareDichotomyDefinitions.Witness (pairedLeaf D oldStep rawLeaf) s t parameter))) :
    Nonempty (Derivation body Delta (Witness D oldStep rawLeaf s t parameter)) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialElimination h
  change Derivation body
    (OriginalLambdaErasureSquareDichotomyDefinitions.WitnessMatrix (pairedLeaf D oldStep rawLeaf) s t parameter :: Delta.map weaken)
    ((Witness D oldStep rawLeaf s t parameter).relabel (Sum.inl : alpha → alpha ⊕ Fin 1))
  rw [witnessRename]
  exact Classical.choice (witnessIntro D oldStep rawLeaf (s.relabel Sum.inl) (t.relabel Sum.inl)
    (.var (.inr 0)) (parameter.relabel Sum.inl)
    (certificateRecover D oldStep rawLeaf (s.relabel Sum.inl) (t.relabel Sum.inl) (.var (.inr 0))
      (parameter.relabel Sum.inl) ⟨Derivation.hypothesis List.mem_cons_self⟩))

theorem resultEquivalent (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf : Program 4) (s t parameter oldS oldT : OTerm alpha) :
    Nonempty (Derivation body Delta
      ((Result D oldStep rawLeaf s t parameter oldS oldT).iff
        (OriginalExistentialRankResultDefinitions.Result (pairedLeaf D oldStep rawLeaf) s t parameter oldS oldT))) := by
  let A := Witness D oldStep rawLeaf s t parameter
  let B := OriginalLambdaErasureSquareDichotomyDefinitions.Witness (pairedLeaf D oldStep rawLeaf) s t parameter
  obtain ⟨hf⟩ := witnessToPaired (body := body) (Delta := A :: Delta) D oldStep rawLeaf s t parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := witnessFromPaired (body := body) (Delta := B :: Delta) D oldStep rawLeaf s t parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact orIff (iffSelf _) ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

theorem witnessRawTransport (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf otherRaw : Program 4) (he : Integration.ProgramGraphEquivalent rawLeaf otherRaw)
    (s t parameter : OTerm alpha)
    (h : Nonempty (Derivation body Delta (Witness D oldStep rawLeaf s t parameter))) :
    Nonempty (Derivation body Delta (Witness D oldStep otherRaw s t parameter)) := by
  apply withWitness D oldStep rawLeaf s t parameter _ h
  intro beta j Theta cert hj hc
  rw [witnessRename]
  apply witnessIntro D oldStep otherRaw (s.relabel j) (t.relabel j) cert (parameter.relabel j)
  exact andIntro
    (iffForward (he body beta Theta (numeral 1)
      (Fin.cons (s.relabel j) (Fin.cons (t.relabel j) (Fin.cons cert (Fin.cons (parameter.relabel j) Fin.elim0)))))
      (andLeft hc)) (andRight hc)

theorem resultRawTransport (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf otherRaw : Program 4) (he : Integration.ProgramGraphEquivalent rawLeaf otherRaw)
    (s t parameter oldS oldT : OTerm alpha)
    (h : Nonempty (Derivation body Delta (Result D oldStep rawLeaf s t parameter oldS oldT))) :
    Nonempty (Derivation body Delta (Result D oldStep otherRaw s t parameter oldS oldT)) := by
  let A := equal s t ⊓ OriginalExistentialRankResultDefinitions.RankWitness oldS oldT
  let B := Witness D oldStep rawLeaf s t parameter
  have left : Nonempty (Derivation body (A :: Delta) (Result D oldStep otherRaw s t parameter oldS oldT)) :=
    ⟨orLeft (Derivation.hypothesis List.mem_cons_self)⟩
  have right : Nonempty (Derivation body (B :: Delta) (Result D oldStep otherRaw s t parameter oldS oldT)) := by
    obtain ⟨hw⟩ := witnessRawTransport D oldStep rawLeaf otherRaw he s t parameter
      (show Nonempty (Derivation body (B :: Delta) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact ⟨orRight hw⟩
  obtain ⟨h⟩ := h
  obtain ⟨left⟩ := left
  obtain ⟨right⟩ := right
  exact ⟨disjunctionElimination h (Derivation.implicationIntroduction left) (Derivation.implicationIntroduction right)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasurePackingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasurePackingProof
