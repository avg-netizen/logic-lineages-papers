module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FixedFormulaSubstitution.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitution.GraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FixedFormulaSubstitution.GraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherPrimitivesProof

theorem unaryComputes {arity inputs ctx : Nat} (p : Program arity) (ctag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (raw : List.Vector (Term ctx) inputs) (tag : Nat) (q : Program inputs) (v : Term ctx)
 (hq : Computes p [] q raw v) :
 Computes p [] (unary tag q) raw (unaryValue ctag tag v) := by
 exact LiteralRawMP.DispatcherCombinatorsProof.binary p [] raw HistoryCodec.cons _ _ _ _ _
  (constantValue p [] raw tag) hq (copies p [] HistoryCodec.cons ctag hc (Term.numeral tag ::ᵥ v ::ᵥ nil))

theorem binaryComputes {arity inputs ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (raw : List.Vector (Term ctx) inputs) (tag : Nat) (q r : Program inputs) (v w : Term ctx)
 (hq : Computes p [] q raw v) (hr : Computes p [] r raw w) :
 Computes p [] (binary tag q r) raw (binaryValue ctag atag tag v w) := by
 apply unaryComputes p ctag hc raw tag
 exact LiteralRawMP.DispatcherCombinatorsProof.binary p [] raw HistoryAppend.append _ _ _ _ _ hq hr
  (copies p [] HistoryAppend.append atag ha (v ::ᵥ w ::ᵥ nil))

theorem termComputes {n depth inputs arity ctx : Nat} (e : Environment n depth inputs) (t : Term n)
 (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (raw : List.Vector (Term ctx) inputs) :
 Computes p [] (termProgram e t) raw (termValue ctag atag e raw t) := by
 induction t with
 | var i =>
  cases h : e i with
  | inl j =>
   simpa only [termProgram,termValue,h] using constantValue p [] raw
    (Encodable.encode (GorbowTermPrefixCode.encode (.var j)))
  | inr j => simpa only [termProgram,termValue,h] using projection p [] raw j
 | zero => exact constantValue p [] raw _
 | succ t ih => exact unaryComputes p ctag hc raw 2 _ _ ih
 | add t u ht hu => exact binaryComputes p ctag atag hc ha raw 3 _ _ _ _ ht hu
 | mul t u ht hu => exact binaryComputes p ctag atag hc ha raw 4 _ _ _ _ ht hu
 | universalFunction t ih => exact unaryComputes p ctag hc raw 5 _ _ ih

theorem formulaComputes {n depth inputs arity ctx : Nat} (e : Environment n depth inputs) (f : Formula n)
 (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (raw : List.Vector (Term ctx) inputs) :
 Computes p [] (formulaProgram f e) raw (formulaValue ctag atag raw f e) := by
 induction f generalizing depth with
 | equal t u =>
  exact binaryComputes p ctag atag hc ha raw 0 _ _ _ _
   (termComputes e t p ctag atag hc ha raw) (termComputes e u p ctag atag hc ha raw)
 | universalRelation t => exact unaryComputes p ctag hc raw 1 _ _ (termComputes e t p ctag atag hc ha raw)
 | agent t => exact unaryComputes p ctag hc raw 2 _ _ (termComputes e t p ctag atag hc ha raw)
 | knowledgeAll t => exact unaryComputes p ctag hc raw 3 _ _ (termComputes e t p ctag atag hc ha raw)
 | knowledge t u =>
  exact binaryComputes p ctag atag hc ha raw 4 _ _ _ _
   (termComputes e t p ctag atag hc ha raw) (termComputes e u p ctag atag hc ha raw)
 | truth t => exact unaryComputes p ctag hc raw 5 _ _ (termComputes e t p ctag atag hc ha raw)
 | neg f ih => exact unaryComputes p ctag hc raw 6 _ _ (ih e)
 | imp f g hf hg => exact binaryComputes p ctag atag hc ha raw 7 _ _ _ _ (hf e) (hg e)
 | conj f g hf hg => exact binaryComputes p ctag atag hc ha raw 8 _ _ _ _ (hf e) (hg e)
 | disj f g hf hg => exact binaryComputes p ctag atag hc ha raw 9 _ _ _ _ (hf e) (hg e)
 | all f ih => exact unaryComputes p ctag hc raw 10 _ _ (ih (liftEnvironment e))
 | ex f ih => exact unaryComputes p ctag hc raw 11 _ _ (ih (liftEnvironment e))

theorem internalTerm : Targets.InternalTerm := by
 intro n depth inputs e t arity p tag ctag atag ht hc ha ctx raw
 obtain ⟨h⟩ := termComputes e t p ctag atag hc ha raw tag ht
 exact ⟨Hilbert.Local.finish h⟩
theorem internalFormula : Targets.InternalFormula := by
 intro n depth inputs e f arity p tag ctag atag ht hc ha ctx raw
 obtain ⟨h⟩ := formulaComputes e f p ctag atag hc ha raw tag ht
 exact ⟨Hilbert.Local.finish h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FixedFormulaSubstitution.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FixedFormulaSubstitution.GraphProof
