module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeCoherentChildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredTypedAuxCasesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeCoherentArgumentProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (casesLeast hasRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalOriginalFirstHopCoreProof (literalAddress)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalLiteralAddressedChildHopProof (fiveRename exact_OpenAddressedRawHop)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralRoundLeastTargets (SameLeastOnEdge)
open NumberedWindowInternalLiteralEdgeCoherentChildProof (exact_OpenEdgeCoherentChildHopAtLeast)
open NumberedWindowInternalNeutralFactsTargets (direct)

open NumberedWindowInternalLiteralCoveredTypedAuxCasesProof (ActiveRaw)
open NumberedWindowInternalLiteralCoveredMemo (coveredMemoWindow)
open NumberedWindowInternalLiteralCoveredMemoAuxRowProof (childAtWindow)
open NumberedWindowInternalLiteralAuxFallback (auxiliaryFallback)
open NumberedWindowInternalLiteralBoundedFallback (fallback)
open NumberedWindowInternalLiteralAuxRootLeaf (leafAtAuxiliary)
open NumberedWindowInternalLiteralRootDispatchNumericProof (root)
open NumberedWindowInternalSparseTypedRawChecks (exact_OpenTypedRaw5)

attribute [local irreducible] programGraph
variable {α : Type} {Γ : List (Formula α)}

/-- Bind the actual least values of the child endpoints and unchanged
argument. In this same canonical carrier body the real child edge
and all three exact reports are available together, with the one
exchange coherence condition and the original child admission. -/
theorem exact_OpenEdgeCoherentChildAndArgument
    (cv tv : Program 1) (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (R : Program 5) (c : Nat) (ctx ty dom q w r arg : OTerm α) (goal : Formula α)
    (paid : SameLeastOnEdge C X W s) :
    let L := packedLeastProgram C X W s
    let i := addressScalar cv tv W L
    let raw := rawWithTarget i cv tv R L
    let data := S i cv tv raw L
    let B := sourceBody data c
    D B Γ (unary cv (suc z) ctx) → D B Γ (unary tv (suc z) ty) →
    D B Γ (programGraph R (suc z) ![ctx,ty,q,w,r]) → D B Γ (windowAt W ctx ty r) →
    D B Γ (hasLeast C X W s ctx ty q) → D B Γ (hasLeast C X W s ctx ty r) →
    D B Γ (hasLeast C X W s ctx dom arg) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (a b u : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (leastGraph C X W s (ctx.relabel j) (ty.relabel j) (q.relabel j) a) →
      D B Δ (leastGraph C X W s (ctx.relabel j) (ty.relabel j) (r.relabel j) b) →
      D B Δ (leastGraph C X W s (ctx.relabel j) (dom.relabel j) (arg.relabel j) u) →
      D B Δ (direct data (hop cv tv raw L) c
        (literalAddress (ctx.relabel j) (ty.relabel j) a)
        (literalAddress (ctx.relabel j) (ty.relabel j) b)) →
      D B Δ (goal.relabel j)) → D B Γ goal := by
  intro L i raw data B gc gt held dst source target argument use
  apply exact_OpenAddressedRawHop C X W s cv tv R ctx ty q w r goal gc gt held source target
  intro β j Δ a b keep l rLeast _
  have arg₁ := renameInto argument j Δ keep
  rw [hasRename] at arg₁
  apply casesLeast C X W s (ctx.relabel j) (dom.relabel j) (arg.relabel j) (goal.relabel j) arg₁
  intro γ k Ω u stay checked
  let m := k ∘ j
  have both (f : Formula α) (h : f ∈ Γ) : f.relabel m ∈ Ω := by
    simpa only [m,formulaRelabelComposition] using stay _ (keep f h)
  have l' := renameInto l k Ω stay
  have r' := renameInto rLeast k Ω stay
  rw [leastRename] at l' r'
  have la : D B Ω (leastGraph C X W s (ctx.relabel m) (ty.relabel m) (q.relabel m) (a.relabel k)) := by
    simpa only [m,Term.relabel_relabel] using l'
  have lb : D B Ω (leastGraph C X W s (ctx.relabel m) (ty.relabel m) (r.relabel m) (b.relabel k)) := by
    simpa only [m,Term.relabel_relabel] using r'
  have v := renameInto dst m Ω both
  rw [windowRename] at v
  have c' := renameInto gc m Ω both
  have t' := renameInto gt m Ω both
  simp only [unaryRename,sucRelabel,zRelabel] at c' t'
  have trace := renameInto held m Ω both
  simp only [programRename,fiveRename,sucRelabel,zRelabel] at trace
  have edge := exact_OpenEdgeCoherentChildHopAtLeast cv tv C X W s R c
    (ctx.relabel m) (ty.relabel m) (q.relabel m) (w.relabel m) (r.relabel m) (a.relabel k) (b.relabel k)
    paid c' t' trace la lb v
  have result := use γ m Ω (a.relabel k) (b.relabel k) u both la lb
    (by simpa only [m,Term.relabel_relabel] using checked) edge
  simpa only [m,formulaRelabelComposition] using result

/-- Specialize to the physically selected covered auxiliary child.
Its exact typed raw report already supplies the destination admission;
the caller provides the original address validators and coherence
for the selected exchange, but no separate scalar or window proof. -/
theorem exact_OpenCoveredEdgeCoherentAuxChild
    (C : Program 3) (X : Program 2) (s : Settings) (leaf : Nat → Program 3)
    (other : Program 3) (base : Program 2) (T V cv tv : Program 1)
    (c : Nat) (ctx dom cod q w r arg : OTerm α) (goal : Formula α) :
    let W := coveredMemoWindow C s base T V
    let R := ActiveRaw C s leaf other base T V
    let ty := rawCons dom cod
    let L := packedLeastProgram C X W s
    let i := addressScalar cv tv W L
    let raw := rawWithTarget i cv tv R L
    let data := S i cv tv raw L
    let B := sourceBody data c
    SameLeastOnEdge C X W s →
    D B Γ (unary cv (suc z) ctx) → D B Γ (unary tv (suc z) ty) →
    D B Γ (programGraph R (suc z) ![ctx,ty,q,w,r] ⊓
      (childAtWindow W V ctx dom arg ⊓
        (hasLeast C X W s ctx ty q ⊓ (hasLeast C X W s ctx ty r ⊓ hasLeast C X W s ctx dom arg)))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (a b u : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (leastGraph C X W s (ctx.relabel j) (ty.relabel j) (q.relabel j) a) →
      D B Δ (leastGraph C X W s (ctx.relabel j) (ty.relabel j) (r.relabel j) b) →
      D B Δ (leastGraph C X W s (ctx.relabel j) (dom.relabel j) (arg.relabel j) u) →
      D B Δ (direct data (hop cv tv raw L) c
        (literalAddress (ctx.relabel j) (ty.relabel j) a)
        (literalAddress (ctx.relabel j) (ty.relabel j) b)) →
      D B Δ (goal.relabel j)) → D B Γ goal := by
  intro W R ty L i raw data B paid gc gt bundle use
  obtain ⟨all⟩ := bundle
  have held := Derivation.conjunctionLeft all
  obtain ⟨read⟩ := exact_OpenTypedRaw5 B (root (leafAtAuxiliary leaf)) (auxiliaryFallback (fallback other))
    W V α Γ ctx ty q w r
  let reports := Derivation.implicationElimination (Derivation.conjunctionLeft read) held
  have window : D B Γ (windowAt W ctx ty r) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight reports)⟩
  have least := Derivation.conjunctionRight (Derivation.conjunctionRight all)
  exact exact_OpenEdgeCoherentChildAndArgument cv tv C X W s R c ctx ty dom q w r arg goal paid
    gc gt ⟨held⟩ window ⟨Derivation.conjunctionLeft least⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight least)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight least)⟩ use

#print axioms exact_OpenEdgeCoherentChildAndArgument
#print axioms exact_OpenCoveredEdgeCoherentAuxChild
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeCoherentArgumentProof
