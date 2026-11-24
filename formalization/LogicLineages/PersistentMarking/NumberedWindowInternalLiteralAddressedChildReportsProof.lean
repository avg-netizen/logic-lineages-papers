module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAddressedChildHopProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAddressedChildReportsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalAccessibilityRulesProof (edgeIntroduction)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (casesLeast hasRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons unary hopCodeTerm)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename packedBodyRename edgeCodeRename)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (tripleTerm)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)
open NumberedWindowInternalOriginalFirstHopCoreProof (D literalAddress oneHopProgram)
open NumberedWindowInternalNeutralFactsTargets (direct)
open NumberedWindowInternalLiteralAddressedChildHopProof (OneHop exact_OpenAddressedRawHop)

attribute [local irreducible] programGraph
variable {α : Type} {Γ : List (Formula α)}

theorem oneHopRename {β : Type} (cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (ctx ty a b q w r : OTerm α) (j : α → β) :
    (OneHop cv tv raw least ctx ty a b q w r).relabel j =
      OneHop cv tv raw least (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j)
        (q.relabel j) (w.relabel j) (r.relabel j) := by
  simp only [OneHop,programRename,tripleInputsRename,sucRelabel,zRelabel,literalAddress,
    tripleTerm,rawConsRename,numeralRename,packedBodyRename,List.map_cons,List.map_nil,
    hopCodeTerm,edgeCodeRename]

abbrev S (i cv tv : Program 1) (raw : Program 5) (least : Program 3) :=
  literalData i (addressPositive cv tv raw least)

abbrev hop (cv tv : Program 1) (raw : Program 5) (least : Program 3) :=
  oneHopProgram (addressPositive cv tv raw least)

theorem directFromOne (i cv tv : Program 1) (raw : Program 5) (least : Program 3) (c : Nat)
    (ctx ty a b q w r : OTerm α)
    (held : D (sourceBody (S i cv tv raw least) c) Γ (OneHop cv tv raw least ctx ty a b q w r)) :
    D (sourceBody (S i cv tv raw least) c) Γ
      (direct (S i cv tv raw least) (hop cv tv raw least) c (literalAddress ctx ty a) (literalAddress ctx ty b)) := by
  let R := addressPositive cv tv raw least
  let B := sourceBody (S i cv tv raw least) c
  let x := literalAddress ctx ty a
  let y := literalAddress ctx ty b
  let hd := hopCodeTerm b q w r
  have h : D B Γ (NumberedWindowComputabilityFormulaTargets.accepts (hop cv tv raw least) x hd y) := by
    unfold NumberedWindowComputabilityFormulaTargets.accepts
    unfold OneHop programGraph at held
    exact held
  have primitive := (exact_CertificateRules i (jRaw i) (hop cv tv raw least) (dCore i R permutation)
    false c B α Γ x y hd).2 h
  exact edgeIntroduction primitive

/-- The function obtains its exact original one-hop in the same body
at the two actual least addresses, and the identical raw argument
obtains its own actual least. The caller must still identify these
with any previously held representatives. -/
theorem exact_OpenChildHopAndArgumentLeast (C : Program 3) (X : Program 2) (W : Program 3)
    (s : Settings) (i cv tv : Program 1) (raw : Program 5) (c : Nat)
    (ctx dom cod fn child dst arg : OTerm α) (goal : Formula α) :
    let ty := rawCons dom cod
    let least := packedLeastProgram C X W s
    let B := sourceBody (S i cv tv raw least) c
    D B Γ (unary cv (suc z) ctx) → D B Γ (unary tv (suc z) ty) →
    D B Γ (programGraph raw (suc z) ![ctx,ty,fn,child,dst]) →
    D B Γ (hasLeast C X W s ctx ty fn) → D B Γ (hasLeast C X W s ctx ty dst) →
    D B Γ (hasLeast C X W s ctx dom arg) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (a b u : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (leastGraph C X W s (ctx.relabel j) (ty.relabel j) (fn.relabel j) a) →
      D B Δ (leastGraph C X W s (ctx.relabel j) (ty.relabel j) (dst.relabel j) b) →
      D B Δ (leastGraph C X W s (ctx.relabel j) (dom.relabel j) (arg.relabel j) u) →
      D B Δ (direct (S i cv tv raw least) (hop cv tv raw least) c
        (literalAddress (ctx.relabel j) (ty.relabel j) a) (literalAddress (ctx.relabel j) (ty.relabel j) b)) →
      D B Δ (goal.relabel j)) → D B Γ goal := by
  intro ty least B gc gt step source target argument use
  apply exact_OpenAddressedRawHop C X W s cv tv raw ctx ty fn child dst goal gc gt step source target
  intro β j Δ a b keep left right edge
  have arg₁ := renameInto argument j Δ keep
  rw [hasRename] at arg₁
  apply casesLeast C X W s (ctx.relabel j) (dom.relabel j) (arg.relabel j) (goal.relabel j) arg₁
  intro γ k Ω u stay checked
  let j₀ := k ∘ j
  have retain (f : Formula α) (h : f ∈ Γ) : f.relabel j₀ ∈ Ω := by
    simpa only [j₀,formulaRelabelComposition] using stay _ (keep f h)
  have left' := renameInto left k Ω stay
  have right' := renameInto right k Ω stay
  have edge' := renameInto edge k Ω stay
  rw [leastRename] at left' right'
  rw [oneHopRename] at edge'
  have same := directFromOne i cv tv raw least c ((ctx.relabel j).relabel k) ((ty.relabel j).relabel k)
    (a.relabel k) (b.relabel k) ((fn.relabel j).relabel k) ((child.relabel j).relabel k)
    ((dst.relabel j).relabel k) edge'
  have final := use γ j₀ Ω (a.relabel k) (b.relabel k) u retain
    (by simpa only [j₀,Term.relabel_relabel] using left')
    (by simpa only [j₀,Term.relabel_relabel] using right')
    (by simpa only [j₀,Term.relabel_relabel] using checked)
    (by simpa only [j₀,Term.relabel_relabel] using same)
  simpa only [j₀,formulaRelabelComposition] using final

#print axioms exact_OpenChildHopAndArgumentLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAddressedChildReportsProof
