module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectRawReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectPhysicalReportProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (certificate)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeExists)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseAddressPositiveOpenForwardProof (forward)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (reportsCases)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (someHopCalls)
open NumberedWindowInternalOriginalOneHopInversionProof
  (exact_OneHopProgramElim exact_OneHopRawInversionAtReports)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)
open NumberedWindowInternalOriginalFirstHopCoreProof (D)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalNeutralFactsTargets (direct directData)

attribute [local irreducible] programGraph
variable {α : Type} {Γ : List (Formula α)}

/-- An original direct certificate itself yields the shared packed
context/type, both endpoint coordinates and validators, and the exact
raw hop report. Nothing about endpoint parsing is supplied by the caller. -/
theorem exact_OpenDirectPhysicalReportCases (i cv tv : Program 1) (raw : Program 5)
    (L : Program 3) (c : Nat) (x y : OTerm α) (goal : Formula α) :
    let data := S i cv tv raw L
    let h := hop cv tv raw L
    let B := sourceBody data c
    D B Γ (direct data h c x y) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (w ctx ty before after : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (addressReport (x.relabel j) ctx ty before) →
      D B Δ (addressReport (y.relabel j) ctx ty after) →
      D B Δ (unary cv (suc z) ctx) → D B Δ (unary tv (suc z) ty) →
      D B Δ (someHopCalls raw L ctx ty before w after) →
      D B Δ (goal.relabel j)) → D B Γ goal := by
  intro data h B edge use
  let j : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let k₀ := addressPositive cv tv raw L
  let x' := x.relabel j
  let y' := y.relabel j
  let cert := certificate (directData data h) false c x' y' w
  let Δ := cert :: Γ.map weaken
  have keep (f : Formula α) (hf : f ∈ Γ) : f.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have atCert : D B Δ cert := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have checked := (exact_CertificateRules i (jRaw i) h (dCore i k₀ permutation)
    false c B _ Δ x' y' w).1 atCert
  have held : D B Δ (programGraph h (suc z) ![x',w,y']) := by
    unfold programGraph accepts at *
    exact checked
  have folded := exact_OneHopProgramElim k₀ x' w y' held
  have opened := forward cv tv raw L x' (rawCons w z) y' folded
  have result : D B Δ (goal.relabel j) := by
    apply reportsCases cv tv raw L x' (rawCons w z) y' (goal.relabel j) opened
    intro β k Ω ctx ty before after retain facts
    obtain ⟨row⟩ := facts
    let rest := Derivation.conjunctionRight row
    let mid := Derivation.conjunctionRight rest
    let tail := Derivation.conjunctionRight mid
    have hx : D B Ω (addressReport (x'.relabel k) ctx ty before) :=
      ⟨Derivation.conjunctionLeft row⟩
    have hy : D B Ω (addressReport (y'.relabel k) ctx ty after) :=
      ⟨Derivation.conjunctionLeft rest⟩
    have current := renameInto held k Ω retain
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at current
    have reported := exact_OneHopRawInversionAtReports cv tv raw L
      (x'.relabel k) (w.relabel k) (y'.relabel k) ctx ty before after hx hy current
    let m := k ∘ j
    have saved (f : Formula α) (hf : f ∈ Γ) : f.relabel m ∈ Ω := by
      simpa only [m,formulaRelabelComposition] using retain _ (keep f hf)
    have reply := use β m Ω (w.relabel k) ctx ty before after saved
      (by simpa only [x',m,Term.relabel_relabel] using hx)
      (by simpa only [y',m,Term.relabel_relabel] using hy)
      ⟨Derivation.conjunctionLeft mid⟩ ⟨Derivation.conjunctionLeft tail⟩ reported
    simpa only [m,formulaRelabelComposition] using reply
  obtain ⟨under⟩ := result
  obtain ⟨witness⟩ := edge
  unfold direct at witness
  rw [edgeExists] at witness
  exact ⟨Derivation.existentialElimination witness under⟩

#print axioms exact_OpenDirectPhysicalReportCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectPhysicalReportProof
