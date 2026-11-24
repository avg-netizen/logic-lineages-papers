module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseReinsertProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchQueryCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseSuccessCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof (graph2Rename)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalAcceptanceSupportProof (programCases)
open InternalListCodecSupportProof (consGraph)
open InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open InternalTagArithmeticSyntaxProof (z suc)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalLiteralScratchErase (state)
open NumberedWindowInternalLiteralScratchEraseReinsertProof (reinsertOfMember)
open NumberedWindowInternalScratchQueryCasesProof (queryCases)
open NumberedWindowInternalLiteralCount (permutation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

private def queries : Fin 3 → Program 2 := ![state,leftOf state,rightOf state]

private theorem recover (raw needle : OTerm alpha) (ys : Fin 3 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries i) (ys i) ![raw,needle]))) :
    Nonempty (Derivation body Delta (graph2 state (ys 0) raw needle)) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 0) (ys 1) (ys 2))) := by
  have stateValue : Nonempty (Derivation body Delta (graph2 state (ys 0) raw needle)) := hq 0
  have bit := unaryRecover InternalUnpair.left state (ys 1) (ys 0) ![raw,needle] (hq 1) (hq 0)
  have rem := unaryRecover InternalUnpair.right state (ys 2) (ys 0) ![raw,needle] (hq 2) (hq 0)
  exact ⟨stateValue,reconstructPair (ys 0) (ys 1) (ys 2) bit rem⟩

/-- Choose one actual residual and a genuine reinsertion cons of the same
needle. The checked literal comparator uses the identical original input.
Both witness openings preserve arbitrary object goal and context. -/
theorem successCases (raw needle : OTerm alpha) (goal : Formula alpha)
    (hm : Nonempty (Derivation body Delta (memberGraph raw needle)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Γ : List (Formula beta)) (rest rebuilt : OTerm beta),
      (∀ f ∈ Delta, f.relabel j ∈ Γ) →
      Nonempty (Derivation body Γ (consGraph rebuilt (needle.relabel j) rest)) →
      Nonempty (Derivation body Γ (programGraph permutation (suc z) ![raw.relabel j,rebuilt])) →
      Nonempty (Derivation body Γ (goal.relabel j))) :
    Nonempty (Derivation body Delta goal) := by
  apply queryCases queries ![raw,needle] goal
  intro beta j ys Γ keep hq
  have ht : (fun i => (![raw,needle] i).relabel j) = ![raw.relabel j,needle.relabel j] :=
    binaryInputsRename raw needle j
  rw [ht] at hq
  obtain ⟨hs,hp⟩ := recover (raw.relabel j) (needle.relabel j) ys hq
  have member := renameInto hm j Γ keep
  rw [graphRename] at member
  apply programCases InternalListCodec.consCode ![needle.relabel j,ys 2] _
  intro gamma k Ξ rebuilt keepMore hcons
  rw [binaryInputsRename] at hcons
  have stateK := renameInto hs k Ξ keepMore
  have pairK := renameInto hp k Ξ keepMore
  have memberK := renameInto member k Ξ keepMore
  rw [graph2Rename] at stateK pairK
  rw [graphRename] at memberK
  have comp := reinsertOfMember ((raw.relabel j).relabel k) ((needle.relabel j).relabel k)
    ((ys 0).relabel k) ((ys 1).relabel k) ((ys 2).relabel k) rebuilt stateK pairK memberK hcons
  have keepAll : ∀ f ∈ Delta, f.relabel (k ∘ j) ∈ Ξ := by
    intro f hf
    simpa only [formulaRelabelComposition] using keepMore (f.relabel j) (keep f hf)
  have con : Nonempty (Derivation body Ξ (consGraph rebuilt (needle.relabel (k ∘ j)) ((ys 2).relabel k))) := by
    have cell : Nonempty (Derivation body Ξ (consGraph rebuilt ((needle.relabel j).relabel k)
      ((ys 2).relabel k))) := hcons
    simpa only [Term.relabel_relabel] using cell
  have cmp : Nonempty (Derivation body Ξ (programGraph permutation (suc z) ![raw.relabel (k ∘ j),rebuilt])) := by
    simpa only [Term.relabel_relabel] using comp
  simpa only [formulaRelabelComposition] using next gamma (k ∘ j) Ξ ((ys 2).relabel k) rebuilt keepAll con cmp

#print axioms successCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseSuccessCasesProof
