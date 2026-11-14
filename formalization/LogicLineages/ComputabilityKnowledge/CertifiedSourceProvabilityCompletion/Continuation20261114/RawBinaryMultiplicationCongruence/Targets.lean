module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawBinaryMultiplicationCongruence.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawBinaryMultiplicationCongruence.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof
/-- Both independent operand equalities produce the original binary multiplication equality
at one exact newest CORE/index/fuel, with the explicit constructed certificate.
All term validity and input acceptance assumptions are object-language antecedents. -/
def InternalCongruence : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t t' u u' first second index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag t')
   (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
    (.imp (RawReflexivityDispatcher.valid I.validatorTag u')
     (.imp (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel t t' first)
      (.imp (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel u u' second)
       (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel
        (RawMulRightCongruence.mulRaw I.consTag I.appendTag t u)
        (RawMulRightCongruence.mulRaw I.consTag I.appendTag t' u')
        (certificate I.mpTag I.qtag I.rightLineTag I.equalityLineTag I.reflexivityTag I.consTag I.appendTag
         t t' u u' first second)))))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawBinaryMultiplicationCongruence.Targets
