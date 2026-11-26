module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.GraphProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem computes (f : Formula 1) {n ctx : Nat} (p : Program n) (ptag ctag atag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (raw : Term ctx) :
 Computes p [] (line f) (raw ::ᵥ nil) (lineValue ptag ctag atag f raw) := by
 have hcons (x y : Term ctx) := copies p [] HistoryCodec.cons ctag hc (x ::ᵥ y ::ᵥ nil)
 have hpair (x y : Term ctx) := copies p [] HistoryCodec.pair ptag hp (x ::ᵥ y ::ᵥ nil)
 have hz := constantValue p [] (raw ::ᵥ nil) 0
 have ht := constantValue p [] (raw ::ᵥ nil) (templateCode f)
 have hraw := projection p [] (raw ::ᵥ nil) 0
 have hbin (k : Nat) (l r : Program 1) (lv rv : Term ctx)
  (hl : Computes p [] l (raw ::ᵥ nil) lv) (hr : Computes p [] r (raw ::ᵥ nil) rv) :
  Computes p [] (RawUniversalReplace.binaryRaw k l r) (raw ::ᵥ nil)
   (RawUniversalReplace.binaryValue ctag atag k lv rv) := by
  have happ := binary p [] (raw ::ᵥ nil) HistoryAppend.append l r lv rv _ hl hr
   (copies p [] HistoryAppend.append atag ha (lv ::ᵥ rv ::ᵥ nil))
  exact binary p [] (raw ::ᵥ nil) HistoryCodec.cons _ _ _ _ _ (constantValue p [] _ k) happ (hcons _ _)
 have hi : Computes p [] (instanceProgram f) (raw ::ᵥ nil) (instanceValue ctag atag f raw) :=
  FixedFormulaSubstitution.GraphProof.formulaComputes environment f p ctag atag hc ha (raw ::ᵥ nil)
 have hall := binary p [] (raw ::ᵥ nil) HistoryCodec.cons _ _ _ _ _ (constantValue p [] _ 10) ht (hcons _ _)
 have hf : Computes p [] (formulaProgram f) (raw ::ᵥ nil) (formulaValue ctag atag f raw) :=
  hbin 7 _ _ _ _ hall hi
 have hargTail := binary p [] (raw ::ᵥ nil) HistoryCodec.cons _ _ _ _ _ hraw hz (hcons _ _)
 have hargs := binary p [] (raw ::ᵥ nil) HistoryCodec.cons _ _ _ _ _ ht hargTail (hcons _ _)
 have hrefs := binary p [] (raw ::ᵥ nil) HistoryCodec.pair _ _ _ _ _ hz hz (hpair _ _)
 have har := binary p [] (raw ::ᵥ nil) HistoryCodec.pair _ _ _ _ _ hargs hrefs (hpair _ _)
 have hpay := binary p [] (raw ::ᵥ nil) HistoryCodec.pair _ _ _ _ _ (constantValue p [] _ 13) har (hpair _ _)
 have hrule := binary p [] (raw ::ᵥ nil) HistoryCodec.pair _ _ _ _ _ hz hpay (hpair _ _)
 have hconcl := binary p [] (raw ::ᵥ nil) HistoryCodec.pair _ _ _ _ _ hf hrule (hpair _ _)
 exact binary p [] (raw ::ᵥ nil) HistoryCodec.pair _ _ _ _ _ hz hconcl (hpair _ _)

theorem internalLine : Targets.InternalLine := by
 intro f n p qtag ptag ctag atag hq hp hc ha ctx raw
 obtain ⟨h⟩ := computes f p ptag ctag atag hp hc ha raw qtag hq
 exact ⟨Hilbert.Local.finish h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.GraphProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.GraphProof.computes
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.GraphProof.internalLine
