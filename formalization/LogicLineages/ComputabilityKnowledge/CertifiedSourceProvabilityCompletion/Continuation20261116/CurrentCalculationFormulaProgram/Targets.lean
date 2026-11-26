module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCalculationFormulaProgram.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCalculationFormulaProgram.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence

/-- Exact original calculation formula, not a decoded surrogate. -/
def NativeFormula : Prop := ∀ m (q : Program m) tag (inputs : List.Vector Nat m),
 evaluate (program q) (tag ::ᵥ inputs) =
 Encodable.encode (GorbowFormulaPrefixCode.encode (EffectiveNumeral.calculation tag q inputs))
/-- Actual AST graph with an arbitrary symbolic runtime target tag and inputs.
The evaluator call is the installed q itself. No formula calibration or success
oracle is supplied. Membership is explicitly conditional here; this packet does
not assert existence of a new published source. -/
def InternalFormula : Prop := ∀ arity (p : Program arity) m (q : Program m)
 (tag qtag ctag atag ntag : Nat),
 (nodes p)[tag]? = some ⟨m+1,program q⟩ →
 (nodes p)[qtag]? = some ⟨m,q⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩ →
 ∀ ctx (targetTag : Term ctx) (inputs : List.Vector (Term ctx) m),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call tag (targetTag ::ᵥ inputs))
   (equalValue ctag atag
    (callValue (codecTags ctag atag ntag) targetTag (inputs.map (LiteralNumeralPrefix.numeralCall ntag)))
    (LiteralNumeralPrefix.numeralCall ntag (call qtag inputs)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCalculationFormulaProgram.Targets
