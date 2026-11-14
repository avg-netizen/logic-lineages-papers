module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftAcceptance.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftAcceptance.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof List.Vector SixSol20261113
/-- Actual numeric search at succ(original encoded line). Three validators only;
the concrete candidate bound and existential gap must be discharged internally. -/
def InternalSearch : Prop := ∀ n (p : Program n) (old : Program 1)
 (I : Installation p old), ∀ ctx (t u v : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
    (.imp (RawReflexivityDispatcher.valid I.validatorTag v)
     (.equal (RawNumericSearch.searchCall I.searchTag
      (.succ (RawMulLeftReplace.lineCall I.qtag t u v))
      (RawMulLeftReplace.lineCall I.qtag t u v)) (.succ .zero))))))
/-- Actual original tag12 logical leaf, preserving [phi,t,u] and zero references.
No recognizer, bound, parser or candidate-success premise. -/
def InternalLogical : Prop := ∀ n (p : Program n) (old : Program 1)
 (I : Installation p old), ∀ ctx (t u v : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
    (.imp (RawReflexivityDispatcher.valid I.validatorTag v)
     (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall I.logicalTag
      (RawMulLeftReplace.lineCall I.qtag t u v)) (.succ .zero))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftAcceptance.Targets
