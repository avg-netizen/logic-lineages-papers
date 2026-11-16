module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCalculationFormulaProgram.GraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCalculationFormulaProgram.SymbolicProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence GorbowRegistryTuple FixedFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

theorem templateInputs {m ctx : Nat} (ctag atag : Nat) (result target : Term ctx) (raw : List.Vector (Term ctx) m) :
 (List.Vector.ofFn (fun i : Fin m => (Term.var i.succ.succ : Term (m+2)))).map
  (termValue ctag atag (environment m) (result ::ᵥ target ::ᵥ raw)) = raw := by
 ext i
 simp only [List.Vector.get_map,List.Vector.get_ofFn,termValue,environment,List.Vector.get_cons_succ]

theorem templateValue {arity m ctx : Nat} (p : Program arity) (ctag atag ntag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (result target : Term ctx) (raw : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaValue ctag atag (result ::ᵥ LiteralNumeralPrefix.numeralCall ntag target ::ᵥ raw) (template m) (environment m))
   (equalValue ctag atag (callValue (codecTags ctag atag ntag) target raw) result))) := by
 let J := codecTags ctag atag ntag
 let av := result ::ᵥ LiteralNumeralPrefix.numeralCall ntag target ::ᵥ raw
 let e := environment m
 have htuple : termValue ctag atag e av
  (tupleTerm (List.Vector.ofFn (fun i : Fin m => (Term.var i.succ.succ : Term (m+2)))).toList) = tupleValue J raw.toList := by
  change termValue J.ctag J.atag e av (tupleTerm _) = _
  rw [CurrentCompositionCertificate.CallEncodingProof.tupleMap (J := J)]
  rw [← List.Vector.toList_map,templateInputs]
 have hpmap (x y : Term (m+2)) : termValue ctag atag e av (pairTerm x y) =
  pairValue J (termValue ctag atag e av x) (termValue ctag atag e av y) := rfl
 obtain ⟨harity⟩ := CurrentCompositionCertificate.CallEncodingProof.numeral p ctag atag hc e av m
 obtain ⟨hpair⟩ := CurrentCompositionCertificate.CallEncodingProof.pairCongruence p J hc ha _ _ _ _ harity
  (.logical (.reflexive (pairValue J (LiteralNumeralPrefix.numeralCall ntag target) (tupleValue J raw.toList))))
 obtain ⟨hcall⟩ := CurrentCompositionCertificate.CodecProof.unary p ctag ctag 5 hc hc _ _ hpair
 obtain ⟨hformula⟩ := CurrentCompositionCertificate.CodecProof.binary p ctag atag ctag atag 0 hc ha hc ha _ _ _ _ hcall
  (.logical (.reflexive result))
 have htagInput : (result ::ᵥ LiteralNumeralPrefix.numeralCall ntag target ::ᵥ raw).get (1 : Fin (m+2)) = LiteralNumeralPrefix.numeralCall ntag target := rfl
 simpa only [template,formulaValue,termValue,hpmap,htagInput,
  htuple,environment,Fin.cases_zero,List.Vector.get_cons_zero,List.Vector.get_cons_succ,
  callValue,headerValue,codecTags,J,av,e,equalValue] using (show Nonempty _ from ⟨hformula⟩)

theorem exactInternal : Targets.InternalFormula := by
 intro arity p m q tag qtag ctag atag ntag ht hq hc ha hn ctx target inputs
 obtain ⟨hg⟩ := GraphProof.rawGraph p q tag qtag ctag atag ntag ht hq hc ha hn target inputs
 obtain ⟨hv⟩ := templateValue p ctag atag ntag hc ha (LiteralNumeralPrefix.numeralCall ntag (call qtag inputs))
  target (inputs.map (LiteralNumeralPrefix.numeralCall ntag))
 exact ⟨Logic.trans _ _ _ hg hv⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCalculationFormulaProgram.SymbolicProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCalculationFormulaProgram.SymbolicProof
