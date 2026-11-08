module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationStepPeel
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalGraphCompositionFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem andIntro {p q : Formula α}
    (hp : Nonempty (Derivation body Gamma p)) (hq : Nonempty (Derivation body Gamma q)) :
    Nonempty (Derivation body Gamma (p ⊓ q)) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hq⟩ := hq
  exact ⟨Derivation.conjunctionIntroduction hp hq⟩

theorem andLeft {p q : Formula α} (h : Nonempty (Derivation body Gamma (p ⊓ q))) :
    Nonempty (Derivation body Gamma p) := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.conjunctionLeft h⟩

theorem andRight {p q : Formula α} (h : Nonempty (Derivation body Gamma (p ⊓ q))) :
    Nonempty (Derivation body Gamma q) := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.conjunctionRight h⟩

/-- Simultaneous witnesses come from ORIGINAL Program totality and composition
elimination. The extra zero program is discarded by the original calculus. -/
theorem queryCases {m n : Nat} (qs : Fin n → Program m) (xs : Fin m → OTerm α)
    (psi : Formula α)
    (h : ∀ (β : Type) (j : α → β) (ys : Fin n → OTerm β) (Delta : List (Formula β)),
      (∀ r ∈ Gamma, r.relabel j ∈ Delta) →
      (∀ i, Nonempty (Derivation body Delta
        (programGraph (qs i) (ys i) (fun a => (xs a).relabel j)))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply programCases (.composition (InternalAcceptance.constantZero n) qs) xs _
  intro β j Delta v hj hv
  apply programCompositionCases (InternalAcceptance.constantZero n) qs v
    (fun a => (xs a).relabel j) _ hv
  intro γ k ys Theta hk _ hg
  have hm : ∀ r ∈ Gamma, r.relabel (k ∘ j) ∈ Theta := by
    intro r hr
    simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hk (r.relabel j) (hj r hr)
  have hg' : ∀ i, Nonempty (Derivation body Theta
      (programGraph (qs i) (ys i) (fun a => (xs a).relabel (k ∘ j)))) := by
    intro i
    simpa only [Term.relabel_relabel] using hg i
  simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using h γ (k ∘ j) ys Theta hm hg'

@[simp] theorem graph5Rename {β : Type} (p : Program 5) (out d e s t a : OTerm α) (j : α → β) :
    (graph5 p out d e s t a).relabel j =
      graph5 p (out.relabel j) (d.relabel j) (e.relabel j) (s.relabel j) (t.relabel j) (a.relabel j) := by
  simp only [graph5,programRename,consTermRename,emptyRename]

@[simp] theorem taggedEdgeRename {β : Type}
    (d e arrow s t a certificate k : OTerm α) (j : α → β) :
    (taggedEdge d e arrow s t a certificate k).relabel j =
      taggedEdge (d.relabel j) (e.relabel j) (arrow.relabel j) (s.relabel j)
        (t.relabel j) (a.relabel j) (certificate.relabel j) (k.relabel j) := by
  simp only [taggedEdge,conjunctionRename,graph1Rename,graph2Rename,graph3Rename]

theorem sameAccept {n : Nat} (p q : Program n) (v : OTerm α) (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Gamma (programGraph p v xs)))
    (hq : Nonempty (Derivation body Gamma (programGraph q v xs))) :
    Nonempty (Derivation body Gamma (programGraph (same p q) (suc z) xs)) :=
  binaryValue InternalEqualityTest.equalityTest p q (suc z) v v xs
    (InternalEqualityTestCompositionProof.equalitySelf v) hp hq

/-- Generic rejection law retains the whole original state at every output. -/
theorem rejectedValue (endpoint : Program 5) (state : OTerm α)
    (h : Nonempty (Derivation body Gamma (graph1 (guard endpoint) z state))) :
    Nonempty (Derivation body Gamma (graph1 (transition endpoint) state state)) :=
  zeroBranchIntro (guard endpoint) (.projection 0) peeledState state (Fin.cons state Fin.elim0)
    h (projectionValue 0 (Fin.cons state Fin.elim0))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
