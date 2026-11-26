module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendAgreementArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendAgreementProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountConsAgreementProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalApplicationValidityStackAppendListProof (consBackward appendZeroValue)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralCountAppendCoreProof (appended)
open NumberedWindowInternalLiteralCountAppendAgreementProof
  (exact_LiteralCommonPrefixCongruence exact_LiteralCommonPrefixCancellation)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem tapeTwo (a b : OTerm α) :
    (![a,b] : Fin 2 → OTerm α) = Fin.cons a (Fin.cons b Fin.elim0) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i

/-- An actual physical cons is the same output as the original append of
the actual singleton and its actual tail. No program equality is assumed. -/
theorem singletonAppend (head single tail out : OTerm α)
    (h : Nonempty (Derivation B Γ (consGraph single head z)))
    (o : Nonempty (Derivation B Γ (consGraph out head tail))) :
    Nonempty (Derivation B Γ (appended single tail out)) := by
  simpa only [appended,tapeTwo] using
    consBackward single head z tail tail out h (appendZeroValue tail) o

/-- Same visible head introduction for exact multiplicity comparison. -/
theorem exact_LiteralConsCongruence (head left right lc rc : OTerm α)
    (l : Nonempty (Derivation B Γ (consGraph lc head left)))
    (r : Nonempty (Derivation B Γ (consGraph rc head right)))
    (h : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![left,right]))) :
    Nonempty (Derivation B Γ (programGraph permutation (suc z) ![lc,rc])) := by
  apply programCases consCode ![head,z] _
  intro β j Δ single keep cell
  rw [binaryInputsRename,zRelabel] at cell
  simp only [programRename,binaryInputsRename,sucRelabel,zRelabel]
  have l' := renameInto l j Δ keep
  have r' := renameInto r j Δ keep
  rw [consGraphRename] at l' r'
  have s : Nonempty (Derivation B Δ (consGraph single (head.relabel j) z)) := by
    simpa only [consGraph,tapeTwo] using cell
  have h' : Nonempty (Derivation B Δ (programGraph permutation (suc z)
      ![left.relabel j,right.relabel j])) := by
    simpa only [sucRelabel,zRelabel] using renamePair permutation (suc z) left right h j keep
  exact exact_LiteralCommonPrefixCongruence single (left.relabel j) (right.relabel j)
    (lc.relabel j) (rc.relabel j)
    (singletonAppend (head.relabel j) single (left.relabel j) (lc.relabel j) s l')
    (singletonAppend (head.relabel j) single (right.relabel j) (rc.relabel j) s r') h'

/-- Same visible head cancellation for exact multiplicity comparison. -/
theorem exact_LiteralConsCancellation (head left right lc rc : OTerm α)
    (l : Nonempty (Derivation B Γ (consGraph lc head left)))
    (r : Nonempty (Derivation B Γ (consGraph rc head right)))
    (h : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![lc,rc]))) :
    Nonempty (Derivation B Γ (programGraph permutation (suc z) ![left,right])) := by
  apply programCases consCode ![head,z] _
  intro β j Δ single keep cell
  rw [binaryInputsRename,zRelabel] at cell
  simp only [programRename,binaryInputsRename,sucRelabel,zRelabel]
  have l' := renameInto l j Δ keep
  have r' := renameInto r j Δ keep
  rw [consGraphRename] at l' r'
  have s : Nonempty (Derivation B Δ (consGraph single (head.relabel j) z)) := by
    simpa only [consGraph,tapeTwo] using cell
  have h' : Nonempty (Derivation B Δ (programGraph permutation (suc z)
      ![lc.relabel j,rc.relabel j])) := by
    simpa only [sucRelabel,zRelabel] using renamePair permutation (suc z) lc rc h j keep
  exact exact_LiteralCommonPrefixCancellation single (left.relabel j) (right.relabel j)
    (lc.relabel j) (rc.relabel j)
    (singletonAppend (head.relabel j) single (left.relabel j) (lc.relabel j) s l')
    (singletonAppend (head.relabel j) single (right.relabel j) (rc.relabel j) s r') h'

#print axioms exact_LiteralConsCongruence
#print axioms exact_LiteralConsCancellation
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountConsAgreementProof
