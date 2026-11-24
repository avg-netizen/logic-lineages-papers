module

public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalFirstHopCoreProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAddressedChildHopProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (casesLeast hasRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons unary hopCodeTerm)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathAdvanceTargets (actualCalls)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalParameterizedAddressPositive (exact_OriginalAddressAt)
open NumberedWindowInternalSparseAddressSingletonTargets (singletonCertificate)
open NumberedWindowInternalSparseAddressSingletonChecks (exact_OpenSingletonCore)
open NumberedWindowInternalOriginalFirstHopCoreProof
  (D literalAddress oneHopProgram exact_OriginalLiteralAddressReport exact_OriginalAddressAtIntro exact_OneHopProgramIntro)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem fiveRename {β : Type} (a b c d e : OTerm α) (j : α → β) :
    (fun i : Fin 5 => ((![a,b,c,d,e] : Fin 5 → OTerm α) i).relabel j) =
      ![a.relabel j,b.relabel j,c.relabel j,d.relabel j,e.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (fun k => Fin.elim0 k))))) i

abbrev OneHop (cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (ctx ty before after q w r : OTerm α) : Formula α :=
  programGraph (oneHopProgram (addressPositive cv tv raw least)) (suc z)
    ![literalAddress ctx ty before,hopCodeTerm after q w r,literalAddress ctx ty after]

/-- The actual original direct checker at the two exact least
representatives accepts the literal child certificate on the same
raw tape. The context/type validators remain actual graph premises. -/
theorem exact_OpenOneHopFromLeastTapes (cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (ctx ty a b q w r : OTerm α)
    (gc : D B Γ (unary cv (suc z) ctx)) (gt : D B Γ (unary tv (suc z) ty))
    (calls : D B Γ (actualCalls raw least ctx ty a b q w r)) :
    D B Γ (OneHop cv tv raw least ctx ty a b q w r) := by
  obtain ⟨support⟩ := exact_OpenSingletonCore B raw least α ctx ty a b q w r
  have check := closedApply ⟨support⟩ calls
  let x := literalAddress ctx ty a
  let y := literalAddress ctx ty b
  have full := exact_OriginalAddressAtIntro cv tv (positive raw least) x (singletonCertificate b q w r) y
    ctx ty a b (exact_OriginalLiteralAddressReport ctx ty a) (exact_OriginalLiteralAddressReport ctx ty b)
    gc gt check
  rw [exact_OriginalAddressAt] at full
  exact exact_OneHopProgramIntro (addressPositive cv tv raw least) x (hopCodeTerm b q w r) y full

/-- Bind both actual child least computations and construct the physical
one-hop check. There is no assumption that either least equals an
unrelated representative previously supplied by the caller. -/
theorem exact_OpenAddressedRawHop (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (cv tv : Program 1) (raw : Program 5) (ctx ty q w r : OTerm α) (goal : Formula α)
    (gc : D B Γ (unary cv (suc z) ctx)) (gt : D B Γ (unary tv (suc z) ty))
    (step : D B Γ (programGraph raw (suc z) ![ctx,ty,q,w,r]))
    (source : D B Γ (hasLeast C X W s ctx ty q)) (target : D B Γ (hasLeast C X W s ctx ty r))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (a b : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (leastGraph C X W s (ctx.relabel j) (ty.relabel j) (q.relabel j) a) →
      D B Δ (leastGraph C X W s (ctx.relabel j) (ty.relabel j) (r.relabel j) b) →
      D B Δ (OneHop cv tv raw (packedLeastProgram C X W s)
        (ctx.relabel j) (ty.relabel j) a b (q.relabel j) (w.relabel j) (r.relabel j)) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  apply casesLeast C X W s ctx ty q goal source
  intro β j Δ a keep la
  have target' := renameInto target j Δ keep
  rw [hasRename] at target'
  apply casesLeast C X W s (ctx.relabel j) (ty.relabel j) (r.relabel j)
    (goal.relabel j) target'
  intro γ k Ω b stay lb
  let l := k ∘ j
  have both (f : Formula α) (hf : f ∈ Γ) : f.relabel l ∈ Ω := by
    simpa only [l,formulaRelabelComposition] using stay _ (keep f hf)
  have qLeast := renameInto la k Ω stay
  rw [leastRename] at qLeast
  have la' : D B Ω (leastGraph C X W s (ctx.relabel l) (ty.relabel l) (q.relabel l) (a.relabel k)) := by
    simpa only [l,Term.relabel_relabel] using qLeast
  have lb' : D B Ω (leastGraph C X W s (ctx.relabel l) (ty.relabel l) (r.relabel l) b) := by
    simpa only [l,Term.relabel_relabel] using lb
  have c := renameInto gc l Ω both
  have t := renameInto gt l Ω both
  have h := renameInto step l Ω both
  simp only [unaryRename,sucRelabel,zRelabel] at c t
  simp only [programRename,fiveRename,sucRelabel,zRelabel] at h
  obtain ⟨aCall⟩ := la'
  obtain ⟨bCall⟩ := lb'
  obtain ⟨rCall⟩ := h
  have hit := exact_OpenOneHopFromLeastTapes cv tv raw (packedLeastProgram C X W s)
    (ctx.relabel l) (ty.relabel l) (a.relabel k) b (q.relabel l) (w.relabel l) (r.relabel l)
    c t ⟨Derivation.conjunctionIntroduction rCall (Derivation.conjunctionIntroduction aCall bCall)⟩
  have out := use γ l Ω (a.relabel k) b both ⟨aCall⟩ ⟨bCall⟩ hit
  simpa only [l,formulaRelabelComposition] using out

#print axioms exact_OpenOneHopFromLeastTapes
#print axioms exact_OpenAddressedRawHop
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAddressedChildHopProof
