module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPositiveEndpointGuardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAddressedChildReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralGuardedPositiveRowsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (edge certificate)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeExists)
open ID1Completion.InternalAccessibilityRulesProof (edgeIntroduction)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseAddressPositiveOpenForwardProof (forward)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (reportsCases)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralPositiveEndpointGuardProof
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowComputabilityFormulaTargets (accepts)

attribute [local irreducible] programGraph
abbrev D (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)
variable {α : Type} {Γ : List (Formula α)}

/-- The true positive path certificate from the installed body already
exposes both exact outer address reports and the actual nonempty fold
on the same type and context. This is the input-side positive lifting
boundary, with no argument lift or matched path asserted yet. -/
theorem exact_OpenGuardedPositiveCertificateRows (i cv tv : Program 1) (raw : Program 5)
    (L : Program 3) (c : Nat) (x y : OTerm α) (goal : Formula α) :
    let data := literalData i (positiveEndpointGuard i (addressPositive cv tv raw L))
    let B := sourceBody data c
    D B Γ (edge data false c x y) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (ctx ty before after path : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (addressReport (x.relabel j) ctx ty before) →
      D B Δ (addressReport (y.relabel j) ctx ty after) →
      D B Δ (unary i (suc z) (x.relabel j)) → D B Δ (unary i (suc z) (y.relabel j)) →
      D B Δ (unary cv (suc z) ctx) → D B Δ (unary tv (suc z) ty) →
      D B Δ (programGraph (positive raw L) (suc z) ![ctx,ty,before,path,after]) →
      D B Δ (goal.relabel j)) → D B Γ goal := by
  intro data B actual use
  let j : α → α ⊕ Fin 1 := Sum.inl
  let path : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let P := addressPositive cv tv raw L
  let R := positiveEndpointGuard i P
  let x' := x.relabel j
  let y' := y.relabel j
  let fact := certificate data false c x' y' path
  let Δ := fact :: Γ.map weaken
  have cert : D B Δ fact := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have accepted : D B Δ (accepts R x' path y') :=
    (exact_CertificateRules i (jRaw i) R (dCore i R permutation) false c B _ Δ x' y' path).1 cert
  have yes : D B Δ (programGraph R (suc z) ![x',path,y']) := by
    unfold programGraph accepts at *
    exact accepted
  obtain ⟨underlying,source,destination⟩ := exact_OpenPositiveEndpointGuardElim i P x' path y' yes
  have parsed := forward cv tv raw L x' path y' underlying
  have under : D B Δ (goal.relabel j) := by
    apply reportsCases cv tv raw L x' path y' (goal.relabel j) parsed
    intro β k Ω ctx ty before after keep known
    let l := k ∘ j
    have both (f : Formula α) (h : f ∈ Γ) : f.relabel l ∈ Ω := by
      have init : f.relabel j ∈ Δ := List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩)
      simpa only [l,formulaRelabelComposition] using keep _ init
    obtain ⟨row⟩ := known
    let q := Derivation.conjunctionRight row
    let r := Derivation.conjunctionRight q
    let t := Derivation.conjunctionRight r
    have atX : D B Ω (addressReport (x.relabel l) ctx ty before) := by
      simpa only [x',l,Term.relabel_relabel] using
        (⟨Derivation.conjunctionLeft row⟩ : D B Ω (addressReport (x'.relabel k) ctx ty before))
    have atY : D B Ω (addressReport (y.relabel l) ctx ty after) := by
      simpa only [y',l,Term.relabel_relabel] using
        (⟨Derivation.conjunctionLeft q⟩ : D B Ω (addressReport (y'.relabel k) ctx ty after))
    have s := renameInto source k Ω keep
    have d := renameInto destination k Ω keep
    simp only [x',y',l,Term.relabel_relabel,unaryRename,sucRelabel,zRelabel] at s d
    have following := use β l Ω ctx ty before after (path.relabel k) both atX atY s d
      ⟨Derivation.conjunctionLeft r⟩ ⟨Derivation.conjunctionLeft t⟩ ⟨Derivation.conjunctionRight t⟩
    simpa only [l,formulaRelabelComposition] using following
  obtain ⟨needed⟩ := under
  obtain ⟨witness⟩ := actual
  rw [edgeExists] at witness
  exact ⟨Derivation.existentialElimination witness needed⟩

/-- An actual addressed certificate and both scalar endpoints yield
the original object edge for the guarded physical positive checker. -/
theorem exact_OpenGuardedPositiveEdge (i cv tv : Program 1) (raw : Program 5)
    (L : Program 3) (c : Nat) (x path y : OTerm α) :
    let P := addressPositive cv tv raw L
    let R := positiveEndpointGuard i P
    let data := literalData i R
    let B := sourceBody data c
    D B Γ (programGraph P (suc z) ![x,path,y]) →
    D B Γ (unary i (suc z) x) → D B Γ (unary i (suc z) y) → D B Γ (edge data false c x y) := by
  intro P R data B actual source target
  have guarded := exact_OpenPositiveEndpointGuardIntro i P x path y actual source target
  have primitive : D B Γ (accepts R x path y) := by
    unfold programGraph accepts at *
    exact guarded
  exact edgeIntroduction ((exact_CertificateRules i (jRaw i) R (dCore i R permutation)
    false c B α Γ x y path).2 primitive)

#print axioms exact_OpenGuardedPositiveCertificateRows
#print axioms exact_OpenGuardedPositiveEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralGuardedPositiveRowsProof
