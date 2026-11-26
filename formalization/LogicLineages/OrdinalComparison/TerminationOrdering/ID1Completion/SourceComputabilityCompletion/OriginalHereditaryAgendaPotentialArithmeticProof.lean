module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetOrderArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphExtensionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalAdditionLawsProof (add leftSuccessor associativity)
open InternalOriginalOrderSyntaxProof (ltF)
open InternalSquareRootArithmeticSupportProof (orderLeft orderRight strictWeakTrans)
open InternalOriginalPairingOrderArithmeticProof (addWeakBoth addStrictRight)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem doubledGap (s q : OTerm alpha)
 (h : Nonempty (Derivation body Delta (ltF s q))) :
 Nonempty (Derivation body Delta (ltF (suc (add s s)) (add q q))) := by
 have hw := InternalRecursionGraphExtensionSupportProof.successorOrder s q h
 have hsum := addWeakBoth (suc s) q (suc s) q hw hw
 have he : Derivation body Delta (eqn (add (suc s) (suc s)) (suc (suc (add s s)))) :=
   trans (leftSuccessor s (suc s)) (congSuc (addSucc s s))
 have hs : Nonempty (Derivation body Delta (ltF (suc (add s s)) (add (suc s) (suc s)))) :=
   ⟨orderRight _ (symm he) (InternalQuotientComparisonProof.equalToNext (refl (suc (add s s))))⟩
 exact strictWeakTrans _ _ _ hs hsum

theorem replacementGap (s q rest : OTerm alpha)
 (h : Nonempty (Derivation body Delta (ltF s q))) :
 Nonempty (Derivation body Delta (ltF (add (add s s) (add (suc z) rest)) (add (add q q) rest))) := by
 obtain ⟨hh⟩ := addStrictRight (suc (add s s)) (add q q) rest (doubledGap s q h)
 have he : Derivation body Delta
   (eqn (add (add s s) (add (suc z) rest)) (add (suc (add s s)) rest)) :=
   trans (symm (associativity (add s s) (suc z) rest))
     (InternalMultiplicationLawsProof.congAddRight rest (trans (addSucc (add s s) z) (congSuc (addZero (add s s)))))
 exact ⟨orderLeft _ (symm he) hh⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialArithmeticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialArithmeticProof
