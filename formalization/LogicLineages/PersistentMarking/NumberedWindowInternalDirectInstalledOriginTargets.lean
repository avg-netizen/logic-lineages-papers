module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreInstalledCertificateTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectProjectedCertTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInstalledOriginTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules (certificate)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectSharedTapeTargets (Reports)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalDirectTargetMapOriginTargets (originRow)

/-- The unpaid observer bridge, pointwise at exactly a tested target/append pair.
No nominal permutation, multiplicity or count correctness is claimed here. -/
def TargetMemberLaw (count : Program 2) (B : Positive (Fin 1)) : Prop :=
  ∀ (β : Type) (Δ : List (Formula β)) (t joined key : OTerm β),
    Nonempty (Derivation B Δ (programGraph count (suc z) ![t,joined])) →
    Nonempty (Derivation B Δ (memberGraph t key)) →
    Nonempty (Derivation B Δ (memberGraph joined key))

/-- Original odd certificate in the actual selected body, and actual
membership in the parsed target. The positive observer law remains an
explicit premise, and is used only at the actual tested pair. Both branches
are scoped under the object existential and append disjunction. -/
def ExactInstalledSuccessorOrigin : Prop :=
  ∀ (i j : Program 1) (r : Program 3) (count : Program 2) (c : Nat)
    (α : Type) (Γ : List (Formula α))
    (src w dst knownTarget key : OTerm α) (goal : Formula α),
    let S := data i j r (dCore i r count)
    let B := sourceBody S c
    TargetMemberLaw count B →
    Nonempty (Derivation B Γ (certificate S true c src dst w)) →
    Nonempty (Derivation B Γ (unary parser (suc knownTarget) dst)) →
    Nonempty (Derivation B Γ (memberGraph knownTarget key)) →
    (∀ (β : Type) (ρ : α → β) (Δ : List (Formula β))
        (kept removed inserted s t k d a p sk tp : OTerm β),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) →
      Reports count count r B Δ (src.relabel ρ) (dst.relabel ρ)
        kept removed inserted s t k d a p sk tp →
      Nonempty (Derivation B Δ (memberGraph k (key.relabel ρ))) →
      Nonempty (Derivation B Δ (goal.relabel ρ))) →
    (∀ (β : Type) (ρ : α → β) (Δ : List (Formula β))
        (kept removed inserted s t k d a p sk tp row dom cert : OTerm β),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) →
      Reports count count r B Δ (src.relabel ρ) (dst.relabel ρ)
        kept removed inserted s t k d a p sk tp →
      Nonempty (Derivation B Δ (originRow a (key.relabel ρ) row)) →
      NumberedWindowInternalDirectInsertedRowCasesTargets.Reports r B Δ
        removed row d (key.relabel ρ) dom cert →
      Nonempty (Derivation B Δ (goal.relabel ρ))) →
    Nonempty (Derivation B Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInstalledOriginTargets
