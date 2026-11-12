module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationCommutativityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetOrderArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel)
open InternalTagArithmeticSupportProof
open InternalMultiplicationLawsProof
open InternalAdditionLawsProof (add)
open InternalMultiplicationCommutativityProof (multiplicationCommutativity)
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalOriginalPairingOrderArithmeticProof (weakCases weakTransport)
open InternalSquareRootArithmeticSupportProof (orderLeft orderRight)
open InternalUnpairArithmeticProof (leftWeakAdd)
open InternalUnpairReverseBoundsArithmeticProof (weakTrans)
open InternalQuotientComparisonProof (equalToNext)
open InternalPairingSumBoundsArithmeticProof (successorWeak)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Multiplication preserves numeric weak order, including zero factors. -/
theorem mulWeakRight (factor x y : OTerm alpha)
 (h : Nonempty (Derivation body Delta (ltF x (suc y)))) :
 Nonempty (Derivation body Delta (ltF (mul factor x) (suc (mul factor y)))) := by
 apply weakCases x y _ h
 · apply orderCases (ltF x y :: Delta) x y _ ⟨Derivation.hypothesis List.mem_cons_self⟩
   intro beta j Theta gap hj he
   simp only [orderRename,sucRelabel,InternalBetaDivisionSyntaxProof.mulRelabel]
   obtain ⟨he⟩ := he
   obtain ⟨hb⟩ := leftWeakAdd (body := body) (Gamma := Theta) (mul (factor.relabel j) (x.relabel j)) (mul (factor.relabel j) (suc gap))
   have hm : Derivation body Theta (eqn
       (add (mul (factor.relabel j) (x.relabel j)) (mul (factor.relabel j) (suc gap)))
       (mul (factor.relabel j) (y.relabel j))) :=
     trans (symm (distributivity (factor.relabel j) (x.relabel j) (suc gap)))
       (congMulLeft (factor.relabel j) he)
   exact ⟨orderRight _ (congSuc hm) hb⟩
 · exact ⟨equalToNext (congMulLeft factor (Derivation.hypothesis List.mem_cons_self))⟩

theorem mulWeakLeft (x y factor : OTerm alpha)
 (h : Nonempty (Derivation body Delta (ltF x (suc y)))) :
 Nonempty (Derivation body Delta (ltF (mul x factor) (suc (mul y factor)))) :=
 weakTransport (mul x factor) (mul y factor) (mul factor x) (mul factor y)
   ⟨multiplicationCommutativity x factor⟩ ⟨multiplicationCommutativity y factor⟩ (mulWeakRight factor x y h)

theorem stepWeak (b c previous other : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (ltF b (suc c))))
 (hp : Nonempty (Derivation body Delta (ltF previous (suc other)))) :
 Nonempty (Derivation body Delta (ltF (suc (mul b previous)) (suc (suc (mul c other))))) :=
 successorWeak (mul b previous) (mul c other)
   (weakTrans (mul b previous) (mul c previous) (mul c other)
     (mulWeakLeft b c previous hb) (mulWeakRight c previous other hp))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetOrderArithmeticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetOrderArithmeticProof
