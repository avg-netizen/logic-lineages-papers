module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendAlgebraProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendSuffixProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendAgreementProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountEquivalenceProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetRecombineProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalLiteralCountAppendCoreProof (appended)
open NumberedWindowInternalLiteralCountAppendSuffixProof (exact_LiteralCommonSuffixCongruence)
open NumberedWindowInternalLiteralCountAppendAgreementProof (exact_LiteralCommonPrefixCongruence)
open NumberedWindowInternalLiteralCountAppendAlgebraProof (exact_LiteralAppendMiddleInterchange)
open NumberedWindowInternalLiteralCountEquivalenceProof (exact_LiteralObserverTransitivity)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- From actual kept and projected-insertion partitions, compare the old
parsed target with the recombination of the two actual side targets. All
operands/reports are the actual ordered list programs. No raw certificate,
downward/I/J, or reconstruction of an allocation is asserted. -/
theorem exact_LiteralTargetRecombine
    (t kept projected kl kr pl pr keptJoin projectedJoin oldJoin
      keptReplaced wholeReplaced tl tr q : OTerm α)
    (oldAppend : Nonempty (Derivation B Γ (appended kept projected oldJoin)))
    (old : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![t,oldJoin])))
    (ak : Nonempty (Derivation B Γ (appended kl kr keptJoin)))
    (ap : Nonempty (Derivation B Γ (appended pl pr projectedJoin)))
    (fk : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![kept,keptJoin])))
    (fp : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![projected,projectedJoin])))
    (ar : Nonempty (Derivation B Γ (appended keptJoin projected keptReplaced)))
    (aw : Nonempty (Derivation B Γ (appended keptJoin projectedJoin wholeReplaced)))
    (al : Nonempty (Derivation B Γ (appended kl pl tl)))
    (arr : Nonempty (Derivation B Γ (appended kr pr tr)))
    (aq : Nonempty (Derivation B Γ (appended tl tr q))) :
    Nonempty (Derivation B Γ (programGraph permutation (suc z) ![t,q])) := by
  have left := exact_LiteralCommonSuffixCongruence kept keptJoin projected oldJoin keptReplaced
    oldAppend ar fk
  have right := exact_LiteralCommonPrefixCongruence keptJoin projected projectedJoin
    keptReplaced wholeReplaced ar aw fp
  have swap := exact_LiteralAppendMiddleInterchange kl kr pl pr keptJoin projectedJoin tl tr
    wholeReplaced q ak ap al arr aw aq
  exact exact_LiteralObserverTransitivity t wholeReplaced q
    (exact_LiteralObserverTransitivity t keptReplaced wholeReplaced
      (exact_LiteralObserverTransitivity t oldJoin keptReplaced old left) right) swap

#print axioms exact_LiteralTargetRecombine
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetRecombineProof
