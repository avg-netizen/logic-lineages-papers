module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumOrderTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumOrderProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue successorValue outputTransport valueUnique)
open ID1Completion.InternalLessThan (ltTest strictLess)
open ID1Completion.InternalLessThanSupportProof (acceptOfLess rejectOfNotLess lessGraph)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalOriginalOrderProof (orderCases actualOriginalOrderIntroduction)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (trans symm congSuc cancelSuc)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalAdditionLawsProof (leftSuccessor)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseOrderedMinimum
open NumberedWindowInternalSparsePositiveOutputTargets (equivalent)
open NumberedWindowInternalSparseMinimumOrderTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

-- Use the additive gap witness from the original order at both successor codes.
private theorem raiseOrder (h p : OTerm α)
    (less : Nonempty (Derivation body Γ (ltF h p))) :
    Nonempty (Derivation body Γ (ltF (suc h) (suc p))) := by
  apply orderCases Γ h p _ less
  intro β j Δ gap _ ⟨e⟩
  simp only [orderRename,sucRelabel]
  apply actualOriginalOrderIntroduction body β Δ (suc (h.relabel j)) (suc (p.relabel j)) gap
  rw [onEquality]
  exact ⟨trans (leftSuccessor (h.relabel j) (suc gap)) (congSuc e)⟩

private theorem reflectOrder (h p : OTerm α)
    (less : Nonempty (Derivation body Γ (ltF (suc h) (suc p)))) :
    Nonempty (Derivation body Γ (ltF h p)) := by
  apply orderCases Γ (suc h) (suc p) _ less
  intro β j Δ gap _ ⟨e⟩
  rw [orderRename]
  simp only [sucRelabel] at e
  apply actualOriginalOrderIntroduction body β Δ (h.relabel j) (p.relabel j) gap
  rw [onEquality]
  exact ⟨cancelSuc (trans (symm (leftSuccessor (h.relabel j) (suc gap))) e)⟩

attribute [local irreducible] programGraph

private theorem offered (h prior : OTerm α) :
    Nonempty (Derivation body Γ (programGraph offerHead (suc h) ![h,prior])) := by
  apply compositionValue .succ (fun _ : Fin 1 => .projection (0 : Fin 2)) (suc h) ![h,prior] ![h]
    (successorValue ![h])
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 ![h,prior]

private theorem compareValue (h prior out : OTerm α)
    (g : Nonempty (Derivation body Γ (lessGraph out (suc h) prior))) :
    Nonempty (Derivation body Γ (programGraph preferHead out ![h,prior])) := by
  apply compositionValue ltTest ![offerHead,.projection 1] out ![h,prior] ![suc h,prior]
  · exact g
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact offered h prior
    · obtain rfl := Fin.eq_zero j
      exact projectionValue 1 ![h,prior]

private theorem identified (h prior k v : OTerm α)
    (g : Nonempty (Derivation body Γ (update h prior v))) :
    Nonempty (Derivation body Γ (equivalent (update h prior k) (eqn k v))) := by
  obtain ⟨actual⟩ := g
  let A := update h prior k
  let B := eqn k v
  obtain ⟨e⟩ := valueUnique (body := body) (Gamma := A :: Γ) minimumStep (suc k) (suc v) ![h,prior]
    ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp actual A⟩
  have eqValue : Derivation body (B :: Γ) (eqn k v) := Derivation.hypothesis List.mem_cons_self
  obtain ⟨result⟩ := outputTransport minimumStep (suc v) (suc k) ![h,prior]
    ⟨congSuc (symm eqValue)⟩ ⟨addHyp actual B⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction (cancelSuc e))
    (Derivation.implicationIntroduction result)⟩

private abbrev choose := branch preferHead (.projection (1 : Fin 2)) offerHead

theorem emptyUpdate : ExactOpenMinimumEmptyUpdate := by
  intro body α Γ h k
  apply identified h z k h
  exact zeroBranchIntro (.projection (1 : Fin 2)) offerHead choose (suc h) ![h,z]
    (projectionValue 1 ![h,z]) (offered h z)

theorem orderedUpdate : ExactOpenMinimumOrderedUpdate := by
  intro body α Γ h prior k
  let L := strictLess h prior
  let xs := ![h,suc prior]
  have yes : Nonempty (Derivation body (L :: Γ) (update h (suc prior) h)) := by
    apply successorBranchIntro (.projection (1 : Fin 2)) offerHead choose (suc h) prior xs
      (projectionValue 1 xs)
    apply successorBranchIntro preferHead (.projection (1 : Fin 2)) offerHead (suc h) z xs
      _ (offered h (suc prior))
    exact compareValue h (suc prior) (suc z) (acceptOfLess _ _ (raiseOrder h prior
      ⟨Derivation.hypothesis List.mem_cons_self⟩))
  have neg : Nonempty (Derivation body (L.not :: Γ) (ltF (suc h) (suc prior)).not) := by
    let lifted := ltF (suc h) (suc prior)
    have hyp : Derivation body (lifted :: L.not :: Γ) L.not :=
      Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
    obtain ⟨smaller⟩ := reflectOrder (body := body) (Γ := lifted :: L.not :: Γ) h prior
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hyp smaller)⟩
  have no : Nonempty (Derivation body (L.not :: Γ) (update h (suc prior) prior)) := by
    apply successorBranchIntro (.projection (1 : Fin 2)) offerHead choose (suc prior) prior xs
      (projectionValue 1 xs)
    apply zeroBranchIntro preferHead (.projection (1 : Fin 2)) offerHead (suc prior) xs
      _ (projectionValue 1 xs)
    exact compareValue h (suc prior) z (rejectOfNotLess _ _ neg)
  obtain ⟨smaller⟩ := identified h (suc prior) k h yes
  obtain ⟨retained⟩ := identified h (suc prior) k prior no
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction smaller)
    (Derivation.implicationIntroduction retained)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumOrderProof
