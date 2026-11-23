module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptBinaryChoicesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationCertificateConstructors (graph2)
open ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof (graph2Rename)
open ID1Completion.InternalControlGraphSupportProof (emptyRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (consTermRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem binaryCases (p : Program 2) (x y : OTerm α) (goal : Formula α)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (out : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (graph2 p out (x.relabel j) (y.relabel j))) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply programCases p (Fin.cons x (Fin.cons y Fin.elim0)) goal
  intro β j Δ out keep worked
  simp only [consTermRename,emptyRename] at worked
  exact next β j Δ out keep worked

theorem renameBinary {β : Type} {Δ : List (Formula β)} (p : Program 2) (out x y : OTerm α)
    (d : Nonempty (Derivation B Γ (graph2 p out x y))) (j : α → β)
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Nonempty (Derivation B Δ (graph2 p (out.relabel j) (x.relabel j) (y.relabel j))) := by
  simpa only [graph2Rename] using (renameInto d j Δ keep)

/-- Bind two independent real evaluations and one real evaluation using
one of their outputs. The remaining input is an original relabelled term. -/
theorem threeBinaryCases (p q r : Program 2) (a b c d e : OTerm α) (first : Bool) (goal : Formula α)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (x y out : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (graph2 p x (a.relabel j) (b.relabel j))) →
      Nonempty (Derivation B Δ (graph2 q y (c.relabel j) (d.relabel j))) →
      Nonempty (Derivation B Δ (graph2 r out (if first then x else e.relabel j)
        (if first then e.relabel j else y))) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply binaryCases p a b goal
  intro β j Δ x keep hx
  apply binaryCases q (c.relabel j) (d.relabel j) (goal.relabel j)
  intro γ k Ω y retain hy
  let g := k ∘ j
  let X := x.relabel k
  let E := e.relabel g
  let carry := keepThrough j k keep retain
  apply binaryCases r (if first then X else E) (if first then E else y)
    ((goal.relabel j).relabel k)
  intro δ m Θ out keepM hz
  let ρ := m ∘ g
  let retainAll := keepThrough g m carry keepM
  have hp := renameBinary p x (a.relabel j) (b.relabel j) hx (m ∘ k) (keepThrough k m retain keepM)
  have hq := renameBinary q y ((c.relabel j).relabel k) ((d.relabel j).relabel k) hy m keepM
  have px : Nonempty (Derivation B Θ
      (graph2 p (X.relabel m) (a.relabel ρ) (b.relabel ρ))) := by
    simpa only [ρ,g,X,Term.relabel_relabel,Function.comp_assoc] using hp
  have qy : Nonempty (Derivation B Θ
      (graph2 q (y.relabel m) (c.relabel ρ) (d.relabel ρ))) := by
    simpa only [ρ,g,Term.relabel_relabel,Function.comp_assoc] using hq
  have rz : Nonempty (Derivation B Θ (graph2 r out (if first then X.relabel m else e.relabel ρ)
      (if first then e.relabel ρ else y.relabel m))) := by
    cases first <;> simpa only [Bool.false_eq_true,if_false,if_true,ρ,E,Term.relabel_relabel] using hz
  rw [formulaRelabelComposition j k goal,formulaRelabelComposition g m goal]
  exact next δ ρ Θ (X.relabel m) (y.relabel m) out retainAll px qy rz

#print axioms binaryCases
#print axioms renameBinary
#print axioms threeBinaryCases
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptBinaryChoicesProof
