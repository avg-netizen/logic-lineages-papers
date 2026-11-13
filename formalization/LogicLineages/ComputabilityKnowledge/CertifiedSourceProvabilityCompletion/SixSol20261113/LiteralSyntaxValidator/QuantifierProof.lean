module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.QuantifierNodesProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.FormulaBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.QuantifierProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport LiteralSyntaxStep QuantifierOperationalProof

theorem atToken {n ctx : Nat} (p : Program n) (vtag ctag : Nat)
 (hv : (nodes p)[vtag]? = some ⟨2,formulaValidator⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (i : Fin 2) (binder raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaCall vtag binder (quantifiedRaw ctag (10+i.val) raw)) (formulaCall vtag (.succ binder) raw))) := by
 obtain ⟨scanTag,ptag,_,eqtag,hscan,hp,_,heq⟩ := FormulaBindingProof.nodesInstalled p vtag hv
 obtain ⟨itag,ltag,_,rtag,hi,hl,_,hr⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p scanTag hscan
 obtain ⟨stag,hs⟩ := LiteralSyntaxScan.InstalledNodesProof.stepNode p itag hi
 obtain ⟨etag,he⟩ := LiteralSyntaxFrame.StepCases.expandInstalled p stag hs
 obtain ⟨atag,ha⟩ := QuantifierNodesProof.appendInstalled p stag hs
 obtain ⟨hstep⟩ := quantifierStep p stag etag atag ptag ctag hs he ha hp hc binder i
 obtain ⟨hunroll⟩ := scanConsSuccess p scanTag itag ltag ptag rtag ctag stag hscan hi hl hp hr hc hs
  (tasks ptag ctag binder) (tasks ptag ctag (.succ binder)) (Term.numeral (10+i.val)) raw
 have hscanEq := Derivation.mp hunroll hstep
 obtain ⟨hleft⟩ := FormulaBindingProof.binding p vtag scanTag ptag ctag eqtag hv hscan hp hc heq binder (quantifiedRaw ctag (10+i.val) raw)
 obtain ⟨hright⟩ := FormulaBindingProof.binding p vtag scanTag ptag ctag eqtag hv hscan hp hc heq (.succ binder) raw
 have he := HistoryAppend.PositiveProof.binaryCongruence eqtag _ _ (.succ (.zero : Term ctx)) (.succ .zero) hscanEq (.logical (.reflexive _))
 exact ⟨Logic.trans _ _ _ hleft (Logic.trans _ _ _ he (Support.equalitySymmetry _ _ hright))⟩

theorem internalQuantifier : Targets.InternalQuantifier := by
 intro n p vtag ctag hv hc token ht ctx binder raw
 rcases ht with h | h
 · subst token
   exact atToken p vtag ctag hv hc (0 : Fin 2) binder raw
 · subst token
   exact atToken p vtag ctag hv hc (1 : Fin 2) binder raw
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.QuantifierProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.QuantifierProof
