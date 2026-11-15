module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTemplateEncodingTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph FixedFormulaSubstitution FixedTemplateEncodingTargets
/-- Capture-correct lifting of the exact bound-only identity environment. -/
theorem liftBound (n : Nat) : liftEnvironment (boundEnvironment n) = boundEnvironment (n+1) := by
 funext i
 cases i using Fin.cases with
 | zero => rfl
 | succ i => rfl
/-- Primitive list-code arithmetic only, not native syntax validity reflection. -/
theorem numeralAppend {n ctx : Nat} (p : Program n) (atag : Nat)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (xs ys : List Nat) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryAppend.appendCall atag (Term.numeral (n := ctx) (Encodable.encode xs)) (Term.numeral (Encodable.encode ys)))
   (Term.numeral (Encodable.encode (xs ++ ys))))) := by
 obtain ⟨h⟩ := QuotedVerifierMP.QuotationProof.numeralCalculation p atag HistoryAppend.append ha
  (Encodable.encode xs ::ᵥ Encodable.encode ys ::ᵥ nil) ctx
 rw [HistoryRuleSuffix.NativeProof.appendList] at h
 simpa only [HistoryAppend.appendCall,List.Vector.map_cons,List.Vector.map_nil] using (show Nonempty _ from ⟨h⟩)
theorem unary {n ctx : Nat} (p : Program n) (ctag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (tag : Nat) (q : Term ctx) (xs : List Nat)
 (hq : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal q (Term.numeral (Encodable.encode xs)))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (unaryValue ctag tag q) (Term.numeral (Encodable.encode (tag :: xs))))) := by
 have hh := Logic.callCongruence (ctx := ctx) (GorbowPRNumeralCalculation.Theory p) ctag
  (Term.numeral tag ::ᵥ q ::ᵥ nil) (Term.numeral tag ::ᵥ Term.numeral (Encodable.encode xs) ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive _)
   | succ i => cases i using Fin.cases with
     | zero => exact hq
     | succ i => exact Fin.elim0 i)
 obtain ⟨hcoded⟩ := BoundVariableArithmeticProof.numeralCons (ctx := ctx) p ctag hc tag xs
 exact ⟨Logic.trans _ _ _ hh hcoded⟩
theorem binary {n ctx : Nat} (p : Program n) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (tag : Nat) (q r : Term ctx) (xs ys : List Nat)
 (hq : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal q (Term.numeral (Encodable.encode xs))))
 (hr : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal r (Term.numeral (Encodable.encode ys)))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (binaryValue ctag atag tag q r) (Term.numeral (Encodable.encode (tag :: (xs ++ ys)))))) := by
 have hh := Logic.callCongruence (ctx := ctx) (GorbowPRNumeralCalculation.Theory p) atag
  (q ::ᵥ r ::ᵥ nil) (Term.numeral (Encodable.encode xs) ::ᵥ Term.numeral (Encodable.encode ys) ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact hq
   | succ i => cases i using Fin.cases with
     | zero => exact hr
     | succ i => exact Fin.elim0 i)
 obtain ⟨hae⟩ := numeralAppend (ctx := ctx) p atag ha xs ys
 exact unary p ctag hc tag (HistoryAppend.appendCall atag q r) (xs ++ ys) (Logic.trans _ _ _ hh hae)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof
