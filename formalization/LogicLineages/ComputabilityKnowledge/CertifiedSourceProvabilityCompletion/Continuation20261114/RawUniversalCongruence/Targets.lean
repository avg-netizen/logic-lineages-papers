module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
def InternalReflexivity : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
  (RawEqualityComposition.accepted I.universalCoreTag I.consTag I.appendTag index fuel t t
   (RawCumulativeLogical.certificate I.consTag I.reflexivityTag t))))
/-- Syntax congruence of original universalFunction, not evaluation. Both actual
MPs and reflexivity run at the distinct newly installed checker. -/
def InternalCongruence : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u input index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
   (.imp (RawEqualityComposition.accepted I.universalCoreTag I.consTag I.appendTag index fuel t u input)
    (RawEqualityComposition.accepted I.universalCoreTag I.consTag I.appendTag index fuel
     (RawUniversalReplace.universalValue I.consTag t) (RawUniversalReplace.universalValue I.consTag u)
     (certificate I.mpTag I.universalLineTag I.reflexivityTag I.consTag I.appendTag t u input))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence.Targets
