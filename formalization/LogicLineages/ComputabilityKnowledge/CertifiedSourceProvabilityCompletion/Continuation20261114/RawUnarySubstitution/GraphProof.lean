module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitution.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitution.GraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem computes (t : Term 1) {n ctx : Nat} (p : Program n) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (raw : Term ctx) :
 Computes p [] (program t) (raw ::ᵥ nil) (value ctag atag raw t) := by
 have hcons (x y : Term ctx) := copies p [] HistoryCodec.cons ctag hc (x ::ᵥ y ::ᵥ nil)
 induction t with
 | var i => exact projection p [] (raw ::ᵥ nil) 0
 | zero =>
  exact binary p [] (raw ::ᵥ nil) HistoryCodec.cons _ _ _ _ _
   (constantValue p [] _ 1) (constantValue p [] _ 0) (hcons _ _)
 | succ t ih =>
  exact binary p [] (raw ::ᵥ nil) HistoryCodec.cons _ _ _ _ _
   (constantValue p [] _ 2) ih (hcons _ _)
 | add t u ht hu =>
  have happ := binary p [] (raw ::ᵥ nil) HistoryAppend.append _ _ _ _ _ ht hu
   (copies p [] HistoryAppend.append atag ha (value ctag atag raw t ::ᵥ value ctag atag raw u ::ᵥ nil))
  exact binary p [] (raw ::ᵥ nil) HistoryCodec.cons _ _ _ _ _
   (constantValue p [] _ 3) happ (hcons _ _)
 | mul t u ht hu =>
  have happ := binary p [] (raw ::ᵥ nil) HistoryAppend.append _ _ _ _ _ ht hu
   (copies p [] HistoryAppend.append atag ha (value ctag atag raw t ::ᵥ value ctag atag raw u ::ᵥ nil))
  exact binary p [] (raw ::ᵥ nil) HistoryCodec.cons _ _ _ _ _
   (constantValue p [] _ 4) happ (hcons _ _)
 | universalFunction t ih =>
  exact binary p [] (raw ::ᵥ nil) HistoryCodec.cons _ _ _ _ _
   (constantValue p [] _ 5) ih (hcons _ _)

theorem internalGraph : Targets.InternalGraph := by
 intro t n p tag ctag atag ht hc ha ctx raw
 obtain ⟨h⟩ := computes t p ctag atag hc ha raw tag ht
 exact ⟨Hilbert.Local.finish h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitution.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitution.GraphProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitution.GraphProof.computes
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitution.GraphProof.internalGraph
