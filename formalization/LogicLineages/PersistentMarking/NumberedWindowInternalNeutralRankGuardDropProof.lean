module

public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardOrderProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalPresentationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardApplicationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardDropProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalComputabilityDownwardProof (edgeCases)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules exact_DomainRules)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalAtomicRefinement (atSource atTarget)
open NumberedWindowInternalAtomicApplicationShapeObjectControlProof (callSlot)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalNeutralRankGuard
open NumberedWindowInternalNeutralRankGuardApplicationProof (targetReport targetRankCases)
open NumberedWindowInternalNeutralRankGuardOrderProof (exact_OpenRankGuardOrder)
open NumberedWindowInternalNeutralRankTargets

private theorem acceptsGraph {α : Type} (r : Program 3) (x w y : OTerm α) :
    accepts r x w y = programGraph r (suc z) ![x,w,y] := rfl

attribute [local irreducible] programGraph

/-- An actual original accepted certificate retains its witness/tape.
The two held rank outputs recover the real comparison callback. -/
theorem exact_OpenRankGuardDropCertificate
    (i j g : Program 1) (r d : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (k x w y : OTerm α) (goal : Formula α)
    (held : Nonempty (Derivation (sourceBody (data i j (rankEven i g r) d) c) Γ
      (certificate (data i j (rankEven i g r) d) false c x y w)))
    (rankX : Nonempty (Derivation (sourceBody (data i j (rankEven i g r) d) c) Γ
      (positiveRank g k x)))
    (next : ∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (m : OTerm β),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) →
      Nonempty (Derivation (sourceBody (data i j (rankEven i g r) d) c) Δ
        (carrier (data i j (rankEven i g r) d) false c (y.relabel ρ))) →
      Nonempty (Derivation (sourceBody (data i j (rankEven i g r) d) c) Δ
        (positiveRank g m (y.relabel ρ))) →
      Nonempty (Derivation (sourceBody (data i j (rankEven i g r) d) c) Δ (ltF m (k.relabel ρ))) →
      Nonempty (Derivation (sourceBody (data i j (rankEven i g r) d) c) Δ (goal.relabel ρ))) :
    Nonempty (Derivation (sourceBody (data i j (rankEven i g r) d) c) Γ goal) := by
  let R := rankEven i g r
  let S := data i j R d
  let B := sourceBody S c
  let xs : Fin 3 → OTerm α := ![x,w,y]
  have actual := (exact_CertificateRules i j R d false c B α Γ x y w).1 held
  rw [acceptsGraph] at actual
  change Nonempty (Derivation B Γ (programGraph (rankEven i g r) (suc z) xs)) at actual
  rw [rankEven] at actual
  have initial : Nonempty (Derivation B Γ (programGraph (atSource g) (suc k) xs)) :=
    callSlot g 0 (suc k) xs rankX
  let rest := conjunction (targetHasRank g) (conjunction (atTarget i) (lowersRank g))
  have picked := successorBranchElim (atSource g) r (conjunction r rest) (suc z) k xs initial actual
  obtain ⟨both⟩ := conjunctionRecover r rest xs picked
  obtain ⟨result⟩ := conjunctionRecover (targetHasRank g) (conjunction (atTarget i) (lowersRank g))
    xs ⟨Derivation.conjunctionRight both⟩
  obtain ⟨tail⟩ := conjunctionRecover (atTarget i) (lowersRank g)
    xs ⟨Derivation.conjunctionRight result⟩
  have scalar : Nonempty (Derivation B Γ (programGraph (atTarget i) (suc z) xs)) :=
    ⟨Derivation.conjunctionLeft tail⟩
  have order : Nonempty (Derivation B Γ (programGraph (lowersRank g) (suc z) xs)) :=
    ⟨Derivation.conjunctionRight tail⟩
  apply targetRankCases g x w y goal ⟨Derivation.conjunctionLeft result⟩
  intro β ρ Δ m keep rankY
  have s := renameInto scalar ρ Δ keep
  have l := renameInto order ρ Δ keep
  have a := renameInto initial ρ Δ keep
  simp only [xs,programRename,tripleInputsRename,sucRelabel,zRelabel] at s l a
  let ys : Fin 3 → OTerm β := ![x.relabel ρ,w.relabel ρ,y.relabel ρ]
  have b : Nonempty (Derivation B Δ (programGraph (atTarget g) (suc m) ys)) :=
    callSlot g 2 (suc m) ys rankY
  have strict := exact_OpenRankGuardOrder g (x.relabel ρ) (w.relabel ρ) (y.relabel ρ) m
    (k.relabel ρ) b a l
  have check := targetReport i (x.relabel ρ) (w.relabel ρ) (y.relabel ρ) (suc z) s
  exact next β ρ Δ m keep ((exact_DomainRules i j R d false c B β Δ (y.relabel ρ)).2 check)
    rankY strict

/-- Open the actual existential certificate of the same original edge.
No symbolic successor is chosen instead of the given y. -/
theorem exact_OpenRankGuardDrop (i j g : Program 1) (r d : Program 3) (c : Nat) :
    RankDrop (data i j (rankEven i g r) d) g c := by
  intro α Γ k x y goal hEdge rankX next
  let S := data i j (rankEven i g r) d
  apply edgeCases S c x y goal hEdge
  intro β ρ Δ w keep₁ actual
  have rx := renameInto rankX ρ Δ keep₁
  rw [NumberedWindowInternalNeutralRankSyntaxProof.positiveRankRename] at rx
  apply exact_OpenRankGuardDropCertificate i j g r d c β Δ (k.relabel ρ)
    (x.relabel ρ) w (y.relabel ρ) (goal.relabel ρ) actual rx
  intro γ η Ω m keep₂ cy ry lt
  have all : ∀ f ∈ Γ, f.relabel (η ∘ ρ) ∈ Ω := by
    intro f hf
    simpa only [formulaRelabelComposition] using keep₂ (f.relabel ρ) (keep₁ f hf)
  simp only [Term.relabel_relabel] at cy ry lt
  simpa only [formulaRelabelComposition] using next γ (η ∘ ρ) Ω m all cy ry lt

#print axioms exact_OpenRankGuardDropCertificate
#print axioms exact_OpenRankGuardDrop
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardDropProof
