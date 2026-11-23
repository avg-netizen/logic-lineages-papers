module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadConeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadConeNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalConstructorHeadFiniteProof
import LogicLineages.PersistentMarking.NumberedWindowNumeralGraphChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadConeOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalControlGraphSupportProof (equalEqn valueUnique)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalLessThan (ltTest)
open ID1Completion.InternalLessThanEvaluationProof (exactLessThanEvaluation)
open ID1Completion.InternalLessThanProof (lessOfAcceptance)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowNumeralGraphChecks (exact_NumeralGraph)
open NumberedWindowNumeralGraphTargets (inputs)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalConstructorHeadFiniteTargets (D)
open NumberedWindowInternalConstructorHeadFiniteProof (exact_OpenConstructorHeadFiniteCases)
open NumberedWindowCopyAlgorithm (compareRanks)
open NumberedWindowInternalCopyHeadConeNumericProof (rankCone)
open NumberedWindowInternalCopyHeadConeTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem closedGraph (p : Program 2) (a b : Nat) :
    D B Γ (programGraph p (numeral (evaluate p (a ::ᵥ b ::ᵥ List.Vector.nil)))
      (Fin.cons (numeral a) (Fin.cons (numeral b) Fin.elim0))) := by
  let xs := a ::ᵥ b ::ᵥ List.Vector.nil
  have d := exact_NumeralGraph 2 p xs B α Γ
  have tape : (inputs xs : Fin 2 → OTerm α) =
      Fin.cons (numeral a) (Fin.cons (numeral b) Fin.elim0) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  rw [tape] at d
  exact d

private theorem rankOrder (n m : Nat) (small : n < m) :
    D B Γ (ltF (numeral n) (numeral m)) := by
  have d := closedGraph (B := B) (α := α) (Γ := Γ) ltTest n m
  rw [exactLessThanEvaluation,if_pos small] at d
  exact lessOfAcceptance (numeral n) (numeral m) d

private theorem fixedHeads (p : Program 2) (source target : OTerm α) (f g : Nat)
    (eF : D B Γ (eqn source (numeral f))) (eG : D B Γ (eqn target (numeral g)))
    (hit : D B Γ (programGraph p (suc z) ![source,target])) :
    D B Γ (programGraph p (suc z)
      (Fin.cons (numeral f) (Fin.cons (numeral g) Fin.elim0))) := by
  unfold programGraph at hit ⊢
  apply graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula p)
    (suc z) ![source,target] (Fin.cons (numeral f) (Fin.cons (numeral g) Fin.elim0)) _ hit
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change D B Γ (equal source (numeral f))
    rw [equalEqn]
    exact eF
  · obtain rfl := Fin.eq_zero j
    change D B Γ (equal target (numeral g))
    rw [equalEqn]
    exact eG

/-- This continuation consumes a genuine accepted occurrence of the
supplied exact comparison graph, not a closed model's judgment on an
open term. The two configured finite head cases supply the literal
values on which checked finite numeral computations are used. -/
theorem exact_OpenSelectedCopyHeadCone : ExactOpenSelectedCopyHeadCone := by
  intro entries p fit heads B α Γ source target goal inF inG hit next
  apply exact_OpenConstructorHeadFiniteCases heads B α Γ source goal inF
  intro f hf
  let F := eqn source (numeral f)
  apply exact_OpenConstructorHeadFiniteCases heads B α (F :: Γ) target goal (withHyp inG F)
  intro g hg
  let G := eqn target (numeral g)
  let Δ := G :: F :: Γ
  have eF : D B Δ F := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have eG : D B Δ G := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have fixed := fixedHeads p source target f g eF eG (withHyp (withHyp hit F) G)
  cases accepted : compareRanks true entries f g with
  | false =>
    have rejected := closedGraph (B := B) (α := α) (Γ := Δ) p f g
    rw [fit,accepted] at rejected
    obtain ⟨absurd⟩ := valueUnique p (suc z) z
      (Fin.cons (numeral f) (Fin.cons (numeral g) Fin.elim0)) fixed rejected
    exact ⟨Derivation.explosion (sucNeZeroApply absurd)⟩
  | true =>
    obtain ⟨m,n,rf,rg,small⟩ := rankCone entries f g accepted
    exact next f hf g hg m n rf rg (rankOrder n m small)

#print axioms exact_OpenSelectedCopyHeadCone

end LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadConeOpenProof
