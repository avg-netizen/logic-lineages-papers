module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalChoicesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalOriginalPairingOrderArithmeticProof (withHyp formulaCases)
open OriginalTypedDecoderInternalBranchProof

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Proof-side finite disjunction, used only to organize the explicit frozen
arithmetic constructor alternatives. Its last branch is retained literally. -/
def alternatives : (n : Nat) → (Fin n → Formula alpha) → Formula alpha → Formula alpha
  | 0, _, fallback => fallback
  | n + 1, ps, fallback => ps 0 ⊔ alternatives n (fun i => ps i.succ) fallback

theorem alternativesIntro (n : Nat) :
    ∀ (ps : Fin n → Formula alpha) (fallback : Formula alpha) (i : Fin n),
      Nonempty (Derivation body Delta (ps i)) →
      Nonempty (Derivation body Delta (alternatives n ps fallback)) := by
  induction n with
  | zero => intro ps fallback i; exact Fin.elim0 i
  | succ n ih =>
    intro ps fallback i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro ⟨h⟩
      exact ⟨orLeft h⟩
    · intro h
      obtain ⟨d⟩ := ih (fun i => ps i.succ) fallback i h
      exact ⟨orRight d⟩

theorem alternativesFallback (n : Nat) :
    ∀ (ps : Fin n → Formula alpha) (fallback : Formula alpha),
      Nonempty (Derivation body Delta fallback) →
      Nonempty (Derivation body Delta (alternatives n ps fallback)) := by
  induction n with
  | zero => intro ps fallback h; exact h
  | succ n ih =>
    intro ps fallback h
    obtain ⟨d⟩ := ih (fun i => ps i.succ) fallback h
    exact ⟨orRight d⟩

theorem alternativesElim (n : Nat) :
    ∀ (Theta : List (Formula alpha)) (ps : Fin n → Formula alpha)
      (fallback psi : Formula alpha),
      Nonempty (Derivation body Theta (alternatives n ps fallback)) →
      (∀ i, Nonempty (Derivation body Theta ((ps i).imp psi))) →
      Nonempty (Derivation body Theta (fallback.imp psi)) →
      Nonempty (Derivation body Theta psi) := by
  induction n with
  | zero =>
    intro Theta ps fallback psi ⟨h⟩ hs ⟨hf⟩
    exact ⟨Derivation.implicationElimination hf h⟩
  | succ n ih =>
    intro Theta ps fallback psi ⟨h⟩ hs hf
    let rest := alternatives n (fun i => ps i.succ) fallback
    obtain ⟨hl⟩ := hs 0
    obtain ⟨hr⟩ := ih (rest :: Theta) (fun i => ps i.succ) fallback psi
      ⟨Derivation.hypothesis List.mem_cons_self⟩
      (fun i => withHyp (hs i.succ) rest) (withHyp hf rest)
    exact ⟨InternalBetaTotalityProof.disjunctionElimination h hl
      (Derivation.implicationIntroduction hr)⟩

theorem alternativesCases {n : Nat} (ps : Fin n → Formula alpha)
    (fallback psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (alternatives n ps fallback)))
    (known : ∀ (i : Fin n) (Theta : List (Formula alpha)),
      (∀ p ∈ Delta, p ∈ Theta) → Nonempty (Derivation body Theta (ps i)) →
      Nonempty (Derivation body Theta psi))
    (other : ∀ Theta : List (Formula alpha),
      (∀ p ∈ Delta, p ∈ Theta) → Nonempty (Derivation body Theta fallback) →
      Nonempty (Derivation body Theta psi)) :
    Nonempty (Derivation body Delta psi) := by
  apply alternativesElim n Delta ps fallback psi h
  · intro i
    obtain ⟨d⟩ := known i (ps i :: Delta) (fun p hp => List.mem_cons_of_mem _ hp)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction d⟩
  · obtain ⟨d⟩ := other (fallback :: Delta) (fun p hp => List.mem_cons_of_mem _ hp)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalChoicesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalChoicesProof
