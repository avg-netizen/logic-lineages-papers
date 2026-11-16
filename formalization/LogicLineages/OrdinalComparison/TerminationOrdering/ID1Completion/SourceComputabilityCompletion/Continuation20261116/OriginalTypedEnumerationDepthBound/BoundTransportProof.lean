module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.BoundTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (z suc eqn varBind)
open InternalTagArithmeticSupportProof (refl congSuc congTerm)
open InternalAdditionLawsProof (add addSubst)
open InternalOriginalPairingOrderArithmeticProof (strictTransport)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem doubleCongruence (s t : OTerm alpha)
    (h : Nonempty (Derivation body Delta (eqn s t))) :
    Nonempty (Derivation body Delta (eqn (twice s) (twice t))) := by
  obtain ⟨h⟩ := h
  have d := congTerm (add (.var (.inr (0 : Fin 1))) (.var (.inr (0 : Fin 1)))) h
  simp only [addSubst,varBind] at d
  exact ⟨d⟩

theorem termTransport (d s d' s' : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (eqn d d')))
    (hs : Nonempty (Derivation body Delta (eqn s s')))
    (h : Nonempty (Derivation body Delta (termBound d' s'))) :
    Nonempty (Derivation body Delta (termBound d s)) := by
  obtain ⟨he⟩ := doubleCongruence s s' hs
  exact strictTransport d (suc (twice s)) d' (suc (twice s')) hd ⟨congSuc he⟩ h

theorem argumentsTransport (d s d' s' : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (eqn d d')))
    (hs : Nonempty (Derivation body Delta (eqn s s')))
    (h : Nonempty (Derivation body Delta (argumentsBound d' s'))) :
    Nonempty (Derivation body Delta (argumentsBound d s)) := by
  obtain ⟨he⟩ := doubleCongruence s s' hs
  exact strictTransport d (suc (suc (twice s))) d' (suc (suc (twice s'))) hd ⟨congSuc (congSuc he)⟩ h

theorem nilBound : Nonempty (Derivation body Delta (argumentsBound (suc z) z)) := by
  have h := OriginalEnumerationMembership.OrderProof.successorForward (body := body) (Delta := Delta)
    z (suc z) ⟨InternalQuotientComparisonProof.zeroLessSuccessor z⟩
  exact strictTransport (suc z) (suc (suc (twice z))) (suc z) (suc (suc z))
    ⟨refl _⟩ ⟨congSuc (congSuc (InternalAdditionLawsProof.leftZero z))⟩ h

theorem unitBound : Nonempty (Derivation body Delta (termBound (suc z) (suc z))) := by
  have h : Nonempty (Derivation body Delta (argumentsBound z z)) :=
    ⟨InternalQuotientComparisonProof.zeroLessSuccessor (suc (twice z))⟩
  exact ArithmeticProof.unaryGrowth z z h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.BoundTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.BoundTransportProof
