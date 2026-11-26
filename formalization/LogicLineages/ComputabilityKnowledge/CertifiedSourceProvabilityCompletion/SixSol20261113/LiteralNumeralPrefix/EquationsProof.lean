module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.ConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.EquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

theorem zero {n ctx : Nat} (p : Program n) (ntag ctag : Nat)
 (hn : (nodes p)[ntag]? = some ⟨1,numeralCode⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.equal (numeralCall ntag (.zero : Term ctx))
 (HistoryLookup.consCall ctag (Term.numeral 1) .zero))) := by
 have hb := GorbowPRSubtree.Proof.lookupTransport n p ntag ⟨1,numeralCode⟩ 1 ⟨0,base⟩ hn
   (GorbowPRChildTags.Proof.recursionBase 0 base step)
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p ntag 0 base step hn ctx nil
 obtain ⟨he⟩ := binary p (nil : List.Vector (Term ctx) 0) HistoryCodec.cons ctag hc
   (HistoryRuleSuffix.constant 0 1) (HistoryRuleSuffix.constant 0 0) (Term.numeral 1) .zero
   (constantValue p nil 1) (constantValue p nil 0) (ntag+1) hb
 exact ⟨Logic.trans _ _ _ hr he⟩

theorem successor {n ctx : Nat} (p : Program n) (ntag ctag : Nat)
 (hn : (nodes p)[ntag]? = some ⟨1,numeralCode⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (value : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.equal (numeralCall ntag (.succ value))
 (HistoryLookup.consCall ctag (Term.numeral 2) (numeralCall ntag value)))) := by
 have hs := SixSol20261112.Fuel.Equations.recursionStepChild p ntag base step hn
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p ntag 0 base step hn ctx value nil
 let args := value ::ᵥ numeralCall ntag value ::ᵥ nil
 obtain ⟨he⟩ := binary p args HistoryCodec.cons ctag hc
   (HistoryRuleSuffix.constant 2 2) (.projection 1) (Term.numeral 2) (numeralCall ntag value)
   (constantValue p args 2) (projection p args 1) (ntag+stepTag base) hs
 exact ⟨Logic.trans _ _ _ hr he⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.EquationsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.EquationsProof
