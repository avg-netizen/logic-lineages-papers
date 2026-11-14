module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightAcceptance.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightAcceptance.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof List.Vector SixSol20261113
/-- Exact symbolic split of original phi; no validity or occurrence premise. -/
def InternalSplit : Prop := ∀ n (p : Program n) (old : Program 1)
 (I : Installation p old), ∀ ctx (t v : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (RawAddRightReplace.templateValue I.consTag I.appendTag t v)
   (HistoryAppend.appendCall I.appendTag (prefixValue I.consTag I.appendTag t v) v)))
/-- Genuine internal logical acceptance by the ACTUAL finite suffix recognizer:
three validators only; original template extraction, suffix occurrence, count
coverage, search composition and selector acceptance are all proof obligations. -/
def InternalLogical : Prop := ∀ n (p : Program n) (old : Program 1)
 (I : Installation p old), ∀ ctx (t u v : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
    (.imp (RawReflexivityDispatcher.valid I.validatorTag v)
     (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall I.logicalTag
      (RawAddRightReplace.lineCall I.qtag t u v)) (.succ .zero))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightAcceptance.Targets
