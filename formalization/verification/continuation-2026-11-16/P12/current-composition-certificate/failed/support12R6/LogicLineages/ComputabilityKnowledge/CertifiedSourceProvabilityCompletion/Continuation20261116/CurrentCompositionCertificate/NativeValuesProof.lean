module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.SeedInputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.NativeValuesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality
theorem numerals {arity ctx n : Nat} (p : Program arity) (J : Tags)
 (hn : (nodes p)[J.numeralTag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (v : List.Vector Nat n) (i : Fin n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal ((numeralValues J.numeralTag (v.map (Term.numeral (n := ctx)))).get i)
   (rawNumeral ((GorbowPRNumeralCalculation.numeralArguments v).get i)))) := by
 simpa only [numeralValues,GorbowPRNumeralCalculation.numeralArguments,List.Vector.get_map] using
  (ValueTraceProof.numeral (ctx := ctx) p J hn (v.get i))
theorem call {arity ctx n : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hn : (nodes p)[J.numeralTag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (tag : Nat) (a : List.Vector (Term ctx) n) (args : List.Vector (Term 0) n)
 (h : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (a.get i) (rawNumeral (args.get i))))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (callValue J (Term.numeral tag) a) (rawNumeral (GorbowPRDefiningEquations.call tag args)))) := by
 have hh : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (a.get i) ((args.map (rawNumeral (ctx := ctx))).get i))) := by
  intro i
  simpa only [List.Vector.get_map] using h i
 obtain ⟨he⟩ := ValueCongruenceProof.calls p J hc ha (Term.numeral tag) a (args.map rawNumeral) hh
 obtain ⟨hv⟩ := ValueTraceProof.call (ctx := ctx) p J hc ha hn tag args
 exact ⟨Logic.trans _ _ _ he hv⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.NativeValuesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.NativeValuesProof
