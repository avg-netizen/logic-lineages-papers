module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumeralAddition.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumeralAddition.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
/-- Genuine internal arithmetic identity relating the actual successor-prefix
program to the ORIGINAL numeral code of the object-language sum. -/
def InternalPrefixNumeral : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : RawAdditionIteration.Installation p old a x), ∀ ctx (m k : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (RawAdditionIteration.binaryCall I.prefixTag k (LiteralNumeralPrefix.numeralCall I.numeralTag m))
   (LiteralNumeralPrefix.numeralCall I.numeralTag (.add m k))))
/-- Unconditional symbolic closed numeral addition computation, at arbitrary
runtime input values and original checker fuel. Original extracted certificate. -/
def InternalAddition : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : RawAdditionIteration.Installation p old a x), Capability (GorbowPRNumeralCalculation.Theory p) p old a x I
open RawAdditionSource
/-- One finite source is selected BEFORE every runtime raw term/count/certificate.
All prior packages and original singleton families plus genuine addition
computation coexist at identical newest checker/MP/producer witnesses. -/
def OneUniformSource : Prop :=
 ∃ (old oldA : Program 1) (baseX : Program 3) (offset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
   (tagG : Nat) (pG : Program 6) (xtag : Nat),
 ∃ I : RawAdditionIteration.Installation (root pF pR old oldA baseX) old oldA (SaturatedAxiomLeaf.saturated baseX),
 I.utag = GorbowNamedInternalProvability.checkerTag pF ∧
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) ∧
 (∀ v, evaluate oldA v = HistoryDispatcher.arithmeticFunction v) ∧
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) ∧
 LiteralValidatedSource.Retained (logical old) (arithmetic oldA) (SaturatedAxiomLeaf.saturated baseX)
  offset pF pR c tagCK pCK tagG pG ∧
 Packages old oldA baseX offset pF pR c I.mpTag xtag ∧
 SingletonCapabilities (S pF pR (verifier old oldA baseX)) (root pF pR old oldA baseX) old oldA (SaturatedAxiomLeaf.saturated baseX) I ∧
 ComputationCapabilities (S pF pR (verifier old oldA baseX)) (root pF pR old oldA baseX) old oldA (SaturatedAxiomLeaf.saturated baseX) I ∧
 Capability (S pF pR (verifier old oldA baseX)) (root pF pR old oldA baseX) old oldA (SaturatedAxiomLeaf.saturated baseX) I
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumeralAddition.Targets
