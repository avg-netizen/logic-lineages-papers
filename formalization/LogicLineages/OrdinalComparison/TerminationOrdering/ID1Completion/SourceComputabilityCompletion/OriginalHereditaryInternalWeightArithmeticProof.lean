module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLeftSuccessorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open OriginalHereditaryInternalWeightDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof InternalMultiplicationLeftSuccessorProof
open InternalOriginalOrderProof (congAddRight)
open InternalOriginalOrderSyntaxProof (ltF)
open InternalSquareRootArithmeticSupportProof InternalQuotientComparisonProof
open InternalOriginalPairingOrderArithmeticProof
open InternalPairingSumBoundsArithmeticProof InternalUnpairArithmeticProof InternalUnpairReverseBoundsArithmeticProof

theorem twoMul (n : OTerm alpha) : Derivation body Delta (eqn (mul (suc (suc z)) n) (add n n)) :=
 trans (leftSuccessorMultiplication (suc z) n)
   (congAddRight n (trans (leftSuccessorMultiplication z n)
     (trans (congAddRight n (multiplicationLeftZero n)) (leftZero n))))

theorem massLengthSucc (len n : OTerm alpha) : Derivation body Delta
 (eqn (mass (suc len) n) (suc (mass len n))) := leftSuccessor len (add n n)

theorem massCountSucc (len n : OTerm alpha) : Derivation body Delta
 (eqn (mass len (suc n)) (suc (suc (mass len n)))) :=
 trans (congAddLeft len (trans (leftSuccessor n (suc n)) (congSuc (addSucc n n))))
   (trans (addSucc len (suc (add n n))) (congSuc (addSucc len (add n n))))

theorem unarySame (len n : OTerm alpha) : Nonempty (Derivation body Delta
 (ltF (mass len n) (mass len (suc n)))) := by
 have h := rightSuccessor (mass len n) (suc (mass len n)) (Nonempty.intro (equalToNext (refl (mass len n))))
 obtain ⟨h⟩ := h
 exact ⟨orderRight _ (symm (massCountSucc len n)) h⟩

theorem unaryExtended (len n : OTerm alpha) : Nonempty (Derivation body Delta
 (ltF (mass (suc len) n) (mass len (suc n)))) :=
 strictTransport _ _ (suc (mass len n)) (suc (suc (mass len n)))
   ⟨massLengthSucc len n⟩ ⟨massCountSucc len n⟩ ⟨equalToNext (refl _)⟩

theorem massWeak (len a b : OTerm alpha) (h : Nonempty (Derivation body Delta (ltF a (suc b)))) :
 Nonempty (Derivation body Delta (ltF (mass len a) (suc (mass len b)))) :=
 addWeakLeft len (add a a) (add b b) (addWeakBoth a b a b h h)

theorem binaryFirst (len a b : OTerm alpha) : Nonempty (Derivation body Delta
 (ltF (mass len a) (mass len (suc (add a b))))) :=
 weakStrictTrans _ _ _ (massWeak len a (add a b) (leftWeakAdd a b)) (unarySame len (add a b))

theorem binarySecond (len a b : OTerm alpha) : Nonempty (Derivation body Delta
 (ltF (mass len b) (mass len (suc (add a b))))) :=
 weakStrictTrans _ _ _ (massWeak len b (add a b) (rightWeakAdd a b)) (unarySame len (add a b))

theorem deletion (len n : OTerm alpha) : Nonempty (Derivation body Delta
 (ltF (mass len n) (mass (suc len) n))) :=
 ⟨orderRight _ (symm (massLengthSucc len n)) (equalToNext (refl _))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightArithmeticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightArithmeticProof
