module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectRawReportsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredNonLambdaAuxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAddressedChildHopProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralReportedAuxiliaryProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceSyntaxProof (fieldsRename)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux)
open NumberedWindowInternalLiteralAuxRootLeaf (functionLambdaHeader)
open NumberedWindowInternalLiteralAuxRootLeafFieldsProof (rawBottom)
open NumberedWindowInternalLiteralFunctionGuardInversionProof (Parts)
open NumberedWindowInternalLiteralCoveredMemo (coveredMemoWindow)
open NumberedWindowInternalLiteralCoveredMemoAuxRowProof (childAtWindow)
open NumberedWindowInternalLiteralCoveredTypedAuxCasesProof (ActiveRaw)
open NumberedWindowInternalLiteralCoveredNonLambdaAuxProof (exact_OpenCoveredNonLambdaAuxiliary)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalLiteralDirectRawReportsProof (exact_OpenDirectRawReports)
open NumberedWindowInternalNeutralFactsTargets (direct)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem leastRawMove (L : Program 3) (ctx ty raw raw' result : OTerm α)
    (e : D B Γ (eqn raw raw')) (held : D B Γ (programGraph L result ![ctx,ty,raw])) :
    D B Γ (programGraph L result ![ctx,ty,raw']) := by
  unfold programGraph at held ⊢
  apply graphInputTransport B α 3 Γ (OrdinaryArithmetic.graphFormula L)
    result ![ctx,ty,raw] ![ctx,ty,raw'] _ held
  intro i
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun k => Fin.elim0 k) b) a) i
  · change D B Γ (equal ctx ctx); rw [equalEqn]; exact ⟨refl _⟩
  · change D B Γ (equal ty ty); rw [equalEqn]; exact ⟨refl _⟩
  · change D B Γ (equal raw raw'); rw [equalEqn]; exact e

/-- The input is the original addressed direct edge, not a selected
replacement raw step. At an actual raw representative with an open
auxiliary/zero-function-header report, the output is either the
actual original least call on bottom, or the exact typed child with
all three successful least queries in its own existing context. -/
theorem exact_OpenReportedAuxiliaryChildOrBottom
    (C : Program 3) (X : Program 2) (s : Settings)
    (leaf : Nat → Program 3) (other : Program 3) (base : Program 2) (T V i cv tv : Program 1)
    (c : Nat) (x y ctx ty before after : OTerm α) (goal : Formula α) :
    let W := coveredMemoWindow C s base T V
    let R := ActiveRaw C s leaf other base T V
    let L := packedLeastProgram C X W s
    let data := S i cv tv R L
    let B := sourceBody data c
    D B Γ (addressReport x ctx ty before) →
    D B Γ (addressReport y ctx ty after) →
    D B Γ (direct data (hop cv tv R L) c x y) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (cert q w r : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (hopCalls R L (ctx.relabel j) (ty.relabel j) (before.relabel j) cert (after.relabel j) q w r) →
      D B Δ (bit sourceIsAux ![q,w,r] ⊓ programGraph functionLambdaHeader z ![q,w,r])) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (leastGraph C X W s (ctx.relabel j) (ty.relabel j) (rawBottom (ty.relabel j)) (after.relabel j)) →
      D B Δ (goal.relabel j)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (q w r dom cod fn arg child dom' cod' dst arg' : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Parts B Δ q w r dom cod fn arg child dom' cod' dst arg' →
      D B Δ (programGraph R (suc z) ![ctx.relabel j,rawCons dom cod,fn,child,dst] ⊓
        (childAtWindow W V (ctx.relabel j) dom arg ⊓
          (hasLeast C X W s (ctx.relabel j) (rawCons dom cod) fn ⊓
            (hasLeast C X W s (ctx.relabel j) (rawCons dom cod) dst ⊓
              hasLeast C X W s (ctx.relabel j) dom arg)))) →
      D B Δ (goal.relabel j)) →
    D B Γ goal := by
  intro W R L data B left right step recognizes bottom inherits
  apply exact_OpenDirectRawReports i cv tv R L c x y ctx ty before after goal left right step
  intro β j Δ cert q w r keep reported
  obtain ⟨shape⟩ := recognizes β j Δ cert q w r keep reported
  obtain ⟨hit⟩ := reported
  let endpoints := Derivation.conjunctionRight hit
  have held : D B Δ (programGraph R (suc z) ![ctx.relabel j,ty.relabel j,q,w,r]) :=
    ⟨Derivation.conjunctionLeft endpoints⟩
  apply exact_OpenCoveredNonLambdaAuxiliary C X s leaf other base T V
    (ctx.relabel j) (ty.relabel j) q w r (goal.relabel j)
    ⟨Derivation.conjunctionLeft shape⟩ ⟨Derivation.conjunctionRight shape⟩ held
  · intro γ k Ω stay e
    let l := k ∘ j
    have both (f : Formula α) (h : f ∈ Γ) : f.relabel l ∈ Ω := by
      simpa only [l,formulaRelabelComposition] using stay _ (keep f h)
    have retained := renameInto (⟨hit⟩ : D B Δ
      (hopCalls R L (ctx.relabel j) (ty.relabel j) (before.relabel j) cert (after.relabel j) q w r)) k Ω stay
    rw [fieldsRename] at retained
    have report : D B Ω (hopCalls R L (ctx.relabel l) (ty.relabel l) (before.relabel l) (cert.relabel k)
        (after.relabel l) (q.relabel k) (w.relabel k) (r.relabel k)) := by
      simpa only [l,Term.relabel_relabel] using retained
    obtain ⟨a⟩ := report
    have selected := Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight a))
    have eq : D B Ω (eqn (r.relabel k) (rawBottom (ty.relabel l))) := by
      simpa only [l,Term.relabel_relabel] using e
    have exactReport := leastRawMove L (ctx.relabel l) (ty.relabel l) (r.relabel k)
      (rawBottom (ty.relabel l)) (suc (after.relabel l)) eq ⟨selected⟩
    have out := bottom γ l Ω both exactReport
    simpa only [l,formulaRelabelComposition] using out
  · intro _ γ k Ω dom cod fn arg child dom' cod' dst arg' stay fields checked
    let l := k ∘ j
    have both (f : Formula α) (h : f ∈ Γ) : f.relabel l ∈ Ω := by
      simpa only [l,formulaRelabelComposition] using stay _ (keep f h)
    have out := inherits γ l Ω (q.relabel k) (w.relabel k) (r.relabel k)
      dom cod fn arg child dom' cod' dst arg' both fields
      (by simpa only [l,Term.relabel_relabel] using checked)
    simpa only [l,formulaRelabelComposition] using out

#print axioms exact_OpenReportedAuxiliaryChildOrBottom
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralReportedAuxiliaryProof
