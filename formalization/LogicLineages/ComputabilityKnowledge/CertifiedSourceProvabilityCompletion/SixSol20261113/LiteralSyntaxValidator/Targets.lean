module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
/-- All vectors, retaining original raw decoder/default and full formula grammar. -/
def NativeFormula : Prop := ∀ v : List.Vector Nat 2,
 evaluate formulaValidator v = HistoryDispatcher.truth
  (GorbowSyntaxValidation.validFormula (v.get 0)
   ((Encodable.decode (α := List Nat) (v.get 1)).getD []))
/-- EXACT original decodedLine/default behavior, not only encoded well-formed lines. -/
def NativeLine : Prop := ∀ v : List.Vector Nat 1,
 evaluate lineValidator v = HistoryDispatcher.validFunction v
/-- Internal Boolean range, not imported from native calibration. -/
def InternalBoolean : Prop := ∀ n (p : Program n) (vtag : Nat),
 (nodes p)[vtag]? = some ⟨2,formulaValidator⟩ → ∀ ctx (context raw : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.disj (.equal (formulaCall vtag context raw) .zero)
   (.equal (formulaCall vtag context raw) (.succ .zero))))
/-- Actual paired fields at arbitrary internal terms; payload is unrestricted. -/
def InternalLineBinding : Prop := ∀ n (p : Program n) (ltag vtag ptag : Nat),
 (nodes p)[ltag]? = some ⟨1,lineValidator⟩ →
 (nodes p)[vtag]? = some ⟨2,formulaValidator⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ → ∀ ctx (context raw payload : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (lineCall ltag (HistoryKernel.pairCall ptag context (HistoryKernel.pairCall ptag raw payload)))
   (formulaCall vtag context raw)))
/-- Formula-boundary premise is necessary: arbitrary raw left/right split is
not assumed to align with the implication's antecedent. Both validity tests
are actual installed validator calls, not external syntax semantics. -/
def InternalImplicationConclusion : Prop := ∀ n (p : Program n) (vtag atag ctag : Nat),
 (nodes p)[vtag]? = some ⟨2,formulaValidator⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (context antecedent conclusion : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (formulaCall vtag context antecedent) (.succ .zero))
   (.imp (.equal (formulaCall vtag context (binaryRaw atag ctag 7 antecedent conclusion)) (.succ .zero))
    (.equal (formulaCall vtag context conclusion) (.succ .zero)))))
/-- Both original quantifier tokens; exact next-context test equality on all
internal raw codes, with no well-formedness or successful-parse premise. -/
def InternalQuantifier : Prop := ∀ n (p : Program n) (vtag ctag : Nat),
 (nodes p)[vtag]? = some ⟨2,formulaValidator⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ token, token = 10 ∨ token = 11 → ∀ ctx (context raw : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaCall vtag context (quantifiedRaw ctag token raw))
   (formulaCall vtag (.succ context) raw)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.Targets
