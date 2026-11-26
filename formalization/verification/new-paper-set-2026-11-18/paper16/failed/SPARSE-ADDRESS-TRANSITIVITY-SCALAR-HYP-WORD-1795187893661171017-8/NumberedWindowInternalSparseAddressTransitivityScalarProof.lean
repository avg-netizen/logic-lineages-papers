module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityAddressProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityScalarProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.SourcePresentation
open ID1Completion.InternalAccessibilityRules (edge certificate)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeExists edgeSubst)
open ID1Completion.InternalAccessibilityRulesProof (edgeIntroduction)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)
open NumberedWindowInternalPullbackSyntaxProof (acceptsRename)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressTransitivityBinderProof (consume)
open NumberedWindowInternalSparseAddressTransitivityAddressProof (combine)
open NumberedWindowInternalSparseAddressTransitivityTargets

private theorem scalarRename {α β : Type} (S : Data) (c : Nat) (x y : OTerm α) (j : α → β) :
    (edge S false c x y).relabel j = edge S false c (x.relabel j) (y.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (edge S false c x y).subst (fun a => emb (.var (j a))) = _
  rw [edgeSubst, ← termRelabelAsSubst, ← termRelabelAsSubst]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Open the actual scalar coordinate-4 certificate at the same outer c,
then use the original adapter to put its unchanged witness in slot 1. -/
private theorem scalarCases (i j : Program 1) (r d : Program 3) (c : Nat) (x y : OTerm α)
    (goal : Formula α) (known : Nonempty (Derivation body Γ (edge (data i j r d) false c x y)))
    (k : ∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (w : OTerm β),
      (∀ p ∈ Γ, p.relabel ρ ∈ Δ) →
      Nonempty (Derivation body Δ (accepts r (x.relabel ρ) w (y.relabel ρ))) →
      Nonempty (Derivation body Δ (goal.relabel ρ))) :
    Nonempty (Derivation body Γ goal) := by
  rw [edgeExists] at known
  obtain ⟨known⟩ := known
  let S := data i j r d
  let ρ : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let row := certificate S false c (x.relabel ρ) (y.relabel ρ) w
  let Δ := row :: Γ.map weaken
  have hρ (p : Formula α) (hp : p ∈ Γ) : p.relabel ρ ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have live := (exact_CertificateRules i j r d false c body (α ⊕ Fin 1) Δ
    (x.relabel ρ) (y.relabel ρ) w).mp ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨done⟩ := k (α ⊕ Fin 1) ρ Δ w hρ live
  exact ⟨Derivation.existentialElimination known done⟩

private theorem scalarCompose (i j cv tv : Program 1) (d : Program 3) (raw : Program 5) (least : Program 3)
    (c : Nat) (left mid right : OTerm α)
    (a : Nonempty (Derivation body Γ (edge (data i j (addressPositive cv tv raw least) d) false c left mid)))
    (b : Nonempty (Derivation body Γ (edge (data i j (addressPositive cv tv raw least) d) false c mid right))) :
    Nonempty (Derivation body Γ (edge (data i j (addressPositive cv tv raw least) d) false c left right)) := by
  let r := addressPositive cv tv raw least
  let S := data i j r d
  apply scalarCases i j r d c left mid (edge S false c left right) a
  intro β ρ Δ first hρ aa
  rw [scalarRename]
  have second := renameInto b ρ Δ hρ
  rw [scalarRename] at second
  apply scalarCases i j r d c (mid.relabel ρ) (right.relabel ρ)
    (edge S false c (left.relabel ρ) (right.relabel ρ)) second
  intro γ η Θ second hη bb
  rw [scalarRename]
  have aa' := renameInto aa η Θ hη
  rw [acceptsRename] at aa'
  let x := (left.relabel ρ).relabel η
  let y := (right.relabel ρ).relabel η
  have res := combine cv tv raw least x (first.relabel η) ((mid.relabel ρ).relabel η) second y aa' bb
  apply consume r x y (edge S false c x y) res
  intro δ renameCert Ξ cert hλ final
  rw [scalarRename]
  exact edgeIntroduction ((exact_CertificateRules i j r d false c body δ Ξ
    (x.relabel renameCert) (y.relabel renameCert) cert).mpr final)

theorem scalar : ExactInstalledScalarEdgeTransitivity := by
  intro i j cv tv d raw least c α left middle right
  let r := addressPositive cv tv raw least
  let S := data i j r d
  let B := sourceBody S c
  let pair := edge S false c left middle ⊓ edge S false c middle right
  have both : Derivation B [pair] pair := Derivation.hypothesis List.mem_cons_self
  obtain ⟨result⟩ := scalarCompose i j cv tv d raw least c left middle right
    ⟨Derivation.conjunctionLeft both⟩ ⟨Derivation.conjunctionRight both⟩
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityScalarProof
