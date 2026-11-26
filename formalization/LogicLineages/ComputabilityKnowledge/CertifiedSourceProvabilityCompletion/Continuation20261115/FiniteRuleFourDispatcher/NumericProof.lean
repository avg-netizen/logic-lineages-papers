module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.NumericProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open HistoryRuleSuffix
/-- Only actual installed defining equations compute a concrete numeral vector. -/
theorem numerals {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (q : Program arity) (v : List.Vector Nat arity) :
 Computes p G q (v.map (Term.numeral : Nat → Term ctx)) (Term.numeral (evaluate q v)) := by
 intro tag ht
 obtain ⟨h⟩ := QuotedVerifierMP.QuotationProof.numeralCalculation p tag q ht v ctx
 exact ⟨.base h⟩
theorem rightNumeral {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (args : List.Vector (Term ctx) 4) (q : Program 4) (v : Nat)
 (h : Computes p G q args (Term.numeral v)) :
 Computes p G (HistoryDispatcher.right q) args (Term.numeral (Nat.unpair v).2) := by
 apply unary p G args (HistoryDecoder.decoder true) q (Term.numeral v) _ h
 have hn := numerals p G (HistoryDecoder.decoder true) (v ::ᵥ nil)
 simpa only [HistoryDecoder.NativeProof.evaluateDecoder,HistoryDecoder.NativeProof.coordinate,
  List.Vector.map_cons,List.Vector.map_nil,ite_true] using hn
theorem leftNumeral {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (args : List.Vector (Term ctx) 4) (q : Program 4) (v : Nat)
 (h : Computes p G q args (Term.numeral v)) :
 Computes p G (HistoryDispatcher.left q) args (Term.numeral (Nat.unpair v).1) := by
 apply unary p G args (HistoryDecoder.decoder false) q (Term.numeral v) _ h
 have hn := numerals p G (HistoryDecoder.decoder false) (v ::ᵥ nil)
 simpa only [HistoryDecoder.NativeProof.evaluateDecoder,HistoryDecoder.NativeProof.coordinate,
  List.Vector.map_cons,List.Vector.map_nil,Bool.false_eq_true,ite_false] using hn
/-- Original three decoder applications; index/fuel/history remain arbitrary. -/
theorem ruleFour {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (sigma : Sentence) (index fuel history : Term ctx) :
 Computes p G HistoryDispatcher.ruleCode
  (index ::ᵥ fuel ::ᵥ history ::ᵥ Term.numeral (FiniteRuleFourLeaf.lineCode sigma) ::ᵥ nil)
  (Term.numeral 4) := by
 let args := index ::ᵥ fuel ::ᵥ history ::ᵥ Term.numeral (FiniteRuleFourLeaf.lineCode sigma) ::ᵥ nil
 have hl : Computes p G HistoryDispatcher.lineCode args (Term.numeral (FiniteRuleFourLeaf.lineCode sigma)) :=
  projection p G args 3
 have hr := rightNumeral p G args _ _ hl
 have hrr := rightNumeral p G args _ _ hr
 have hv := leftNumeral p G args _ _ hrr
 simpa only [args,HistoryDispatcher.ruleCode,FiniteRuleFourLeaf.lineCode,GorbowTheoryChecker.axiomLine,
  HistoryDispatcher.NativeProof.encodeProd,HistoryDispatcher.NativeProof.encodeNat,Nat.unpair_pair] using hv
/-- Fixed typed formula validity rewrites one installed concrete validator graph. -/
theorem validCanonical (sigma : Sentence) :
 evaluate LiteralSyntaxValidator.lineValidator
  (FiniteRuleFourLeaf.lineCode sigma ::ᵥ nil) = 1 := by
 have hv : GorbowSyntaxValidation.validFormula 0
  (GorbowFormulaPrefixCode.encode (GorbowTheoryProof.weakenClosed 0 sigma)) = true :=
  (GorbowSyntaxValidationProof.exactTypedDomain.2 _ _).mpr
   ⟨_,(GorbowFormulaPrefixCodeProof.decoderExact _ _ _).mpr rfl⟩
 have hh := LiteralSyntaxValidator.NativeProof.lineEncoded (GorbowTheoryChecker.axiomLine 0 sigma)
 change evaluate LiteralSyntaxValidator.lineValidator
  (FiniteRuleFourLeaf.lineCode sigma ::ᵥ nil) = _ at hh
 rw [GorbowTheoryChecker.axiomLine,GorbowProofChecker.context,GorbowProofChecker.conclusion,hv] at hh
 exact hh
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.NumericProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.NumericProof
