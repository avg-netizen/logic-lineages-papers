module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.Definitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.NaturalityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open GorbowSubstitution GorbowFormulaSubstitution FixedFormulaSubstitution SixSol20261112.Fuel
@[simp] theorem termValueSubst {n depth inputs m ctx : Nat} (sub : Fin m → Term ctx) (ctag atag : Nat)
 (e : Environment n depth inputs) (raw : List.Vector (Term m) inputs) (t : Term n) :
 substitute sub (termValue ctag atag e raw t) = termValue ctag atag e (raw.map (substitute sub)) t := by
 induction t with
 | var i => cases he : e i <;> simp only [termValue,he,Logic.substNumeral,List.Vector.get_map]
 | zero => simp only [termValue,Logic.substNumeral]
 | succ t ih => simp only [termValue,unaryValue,HistoryLookup.consCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,Logic.substNumeral,ih]
 | add t u iht ihu => simp only [termValue,binaryValue,unaryValue,HistoryLookup.consCall,HistoryAppend.appendCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,Logic.substNumeral,iht,ihu]
 | mul t u iht ihu => simp only [termValue,binaryValue,unaryValue,HistoryLookup.consCall,HistoryAppend.appendCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,Logic.substNumeral,iht,ihu]
 | universalFunction t ih => simp only [termValue,unaryValue,HistoryLookup.consCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,Logic.substNumeral,ih]

@[simp] theorem unarySubst {m ctx : Nat} (sub : Fin m → Term ctx) (ctag tag : Nat) (a : Term m) :
 substitute sub (unaryValue ctag tag a) = unaryValue ctag tag (substitute sub a) := by
 simp only [unaryValue, HistoryLookup.consCall, termValueSubst, Logic.substCall, List.Vector.map_cons, List.Vector.map_nil, Logic.substNumeral, substitute]

@[simp] theorem binarySubst {m ctx : Nat} (sub : Fin m → Term ctx) (ctag atag tag : Nat) (a b : Term m) :
 substitute sub (FixedFormulaSubstitution.binaryValue ctag atag tag a b) = FixedFormulaSubstitution.binaryValue ctag atag tag (substitute sub a) (substitute sub b) := by
 simp only [FixedFormulaSubstitution.binaryValue, HistoryAppend.appendCall, termValueSubst, unarySubst, Logic.substCall, List.Vector.map_cons, List.Vector.map_nil, Logic.substNumeral, substitute]

@[simp] theorem numeralSubst {m ctx : Nat} (sub : Fin m → Term ctx) (tag : Nat) (a : Term m) :
 substitute sub (LiteralNumeralPrefix.numeralCall tag a) = LiteralNumeralPrefix.numeralCall tag (substitute sub a) := by
 simp only [LiteralNumeralPrefix.numeralCall, termValueSubst, unarySubst, binarySubst, Logic.substCall, List.Vector.map_cons, List.Vector.map_nil, Logic.substNumeral, substitute]

@[simp] theorem mpSubst {m ctx : Nat} (sub : Fin m → Term ctx) (tag : Nat) (context a b c : Term m) :
 substitute sub (LiteralMPRun.certificate tag context a b c) = LiteralMPRun.certificate tag (substitute sub context) (substitute sub a) (substitute sub b) (substitute sub c) := by
 simp only [LiteralMPRun.certificate, termValueSubst, unarySubst, binarySubst, numeralSubst, Logic.substCall, List.Vector.map_cons, List.Vector.map_nil, Logic.substNumeral, substitute]

@[simp] theorem rule12Subst {m ctx : Nat} (sub : Fin m → Term ctx) (ctag tag : Nat) (a b c : Term m) :
 substitute sub (UniformClosedRule12Certificate.certificate ctag tag a b c) = UniformClosedRule12Certificate.certificate ctag tag (substitute sub a) (substitute sub b) (substitute sub c) := by
 simp only [UniformClosedRule12Certificate.certificate, UniformClosedRule12.lineCall, HistoryLookup.consCall, termValueSubst, unarySubst, binarySubst, numeralSubst, mpSubst, Logic.substCall, List.Vector.map_cons, List.Vector.map_nil, Logic.substNumeral, substitute]

@[simp] theorem reflSubst {m ctx : Nat} (sub : Fin m → Term ctx) (K : Tags) (a : Term m) :
 substitute sub (reflexivityCertificate K a) = reflexivityCertificate K (substitute sub a) := by
 simp only [reflexivityCertificate, RawCumulativeLogical.certificate, RawReflexivity.lineCall, HistoryLookup.consCall, termValueSubst, unarySubst, binarySubst, numeralSubst, mpSubst, rule12Subst, Logic.substCall, List.Vector.map_cons, List.Vector.map_nil, Logic.substNumeral, substitute]

@[simp] theorem transSubst {m ctx : Nat} (sub : Fin m → Term ctx) (mtag ctag atag tag : Nat) (a b c hab hbc : Term m) :
 substitute sub (transitivityCertificate mtag ctag atag tag a b c hab hbc) = transitivityCertificate mtag ctag atag tag (substitute sub a) (substitute sub b) (substitute sub c) (substitute sub hab) (substitute sub hbc) := by
 simp only [transitivityCertificate, equalValue, impValue, termValueSubst, unarySubst, binarySubst, numeralSubst, mpSubst, rule12Subst, reflSubst, Logic.substCall, List.Vector.map_cons, List.Vector.map_nil, Logic.substNumeral, substitute]

@[simp] theorem unaryCertSubst {m ctx : Nat} (sub : Fin m → Term ctx) (K : Tags) (f : Term 1) (a b hab : Term m) :
 substitute sub (PrescribedRuntimeCallCongruence.unaryCertificate K f a b hab) = PrescribedRuntimeCallCongruence.unaryCertificate K f (substitute sub a) (substitute sub b) (substitute sub hab) := by
 simp only [PrescribedRuntimeCallCongruence.unaryCertificate, PrescribedRuntimeEquality.unaryCertificate, specializedValue, RawCumulativeLogical.certificate, RawReflexivity.lineCall, HistoryLookup.consCall, equalValue, impValue, termValueSubst, unarySubst, binarySubst, numeralSubst, mpSubst, rule12Subst, reflSubst, transSubst, Logic.substCall, List.Vector.map_cons, List.Vector.map_nil, Logic.substNumeral, substitute]

@[simp] theorem binaryCertSubst {m ctx : Nat} (sub : Fin m → Term ctx) (K : Tags) (mul : Bool) (a b c d hac hbd : Term m) :
 substitute sub (binaryCertificate K mul a b c d hac hbd) = binaryCertificate K mul (substitute sub a) (substitute sub b) (substitute sub c) (substitute sub d) (substitute sub hac) (substitute sub hbd) := by
 simp only [binaryCertificate, PrescribedRuntimeEquality.unaryCertificate, specializedValue, RawCumulativeLogical.certificate, RawReflexivity.lineCall, HistoryLookup.consCall, PrescribedRuntimeCallCongruence.binaryValue, equalValue, impValue, termValueSubst, unarySubst, binarySubst, numeralSubst, mpSubst, rule12Subst, reflSubst, transSubst, unaryCertSubst, Logic.substCall, List.Vector.map_cons, List.Vector.map_nil, Logic.substNumeral, substitute]

@[simp] theorem pairSubst {m ctx : Nat} (sub : Fin m → Term ctx) (K : Tags) (a b : Term m) :
 substitute sub (pairValue K a b) = pairValue K (substitute sub a) (substitute sub b) := by
 simp only [pairValue, PrescribedRuntimeCallCongruence.binaryValue, termValueSubst, unarySubst, binarySubst, numeralSubst, mpSubst, rule12Subst, reflSubst, transSubst, unaryCertSubst, binaryCertSubst, Logic.substCall, List.Vector.map_cons, List.Vector.map_nil, Logic.substNumeral, substitute]

@[simp] theorem pairCertSubst {m ctx : Nat} (sub : Fin m → Term ctx) (K : Tags) (a b c d hac hbd : Term m) :
 substitute sub (pairCertificate K a b c d hac hbd) = pairCertificate K (substitute sub a) (substitute sub b) (substitute sub c) (substitute sub d) (substitute sub hac) (substitute sub hbd) := by
 simp only [pairCertificate, PrescribedRuntimeCallCongruence.binaryValue, termValueSubst, unarySubst, binarySubst, numeralSubst, mpSubst, rule12Subst, reflSubst, transSubst, unaryCertSubst, binaryCertSubst, pairSubst, Logic.substCall, List.Vector.map_cons, List.Vector.map_nil, Logic.substNumeral, substitute]

@[simp] theorem tupleValueSubst {m ctx : Nat} (sub : Fin m → Term ctx) (K : Tags) (xs : List (Term m)) :
 substitute sub (tupleValue K xs) = tupleValue K (xs.map (substitute sub)) := by
 induction xs with
 | nil => simp only [tupleValue,zeroValue,rawNumeral,Logic.substNumeral,List.map_nil]
 | cons a xs ih => simp only [tupleValue,List.map_cons,unarySubst,pairSubst,ih]

@[simp] theorem tupleCertSubst {m ctx n : Nat} (sub : Fin m → Term ctx) (K : Tags)
 (xs ys cs : List.Vector (Term m) n) :
 substitute sub (tupleCertificate K xs ys cs) =
 tupleCertificate K (xs.map (substitute sub)) (ys.map (substitute sub)) (cs.map (substitute sub)) := by
 induction n with
 | zero => simp only [tupleCertificate,reflSubst,zeroValue,rawNumeral,Logic.substNumeral]
 | succ n ih =>
  simp only [tupleCertificate,unaryCertSubst,pairSubst,tupleValueSubst,pairCertSubst,ih,
   List.Vector.head_map,List.Vector.tail_map,List.Vector.toList_map]

@[simp] theorem callValueSubst {m ctx n : Nat} (sub : Fin m → Term ctx) (K : Tags)
 (tag : Term m) (xs : List.Vector (Term m) n) :
 substitute sub (callValue K tag xs) = callValue K (substitute sub tag) (xs.map (substitute sub)) := by
 simp only [callValue,headerValue,unarySubst,pairSubst,numeralSubst,tupleValueSubst,rawNumeral,Logic.substNumeral,List.Vector.toList_map]

@[simp] theorem callCertSubst {m ctx n : Nat} (sub : Fin m → Term ctx) (K : Tags)
 (tag : Term m) (xs ys cs : List.Vector (Term m) n) :
 substitute sub (callCertificate K tag xs ys cs) = callCertificate K (substitute sub tag)
  (xs.map (substitute sub)) (ys.map (substitute sub)) (cs.map (substitute sub)) := by
 simp only [callCertificate,headerValue,unaryCertSubst,pairSubst,numeralSubst,tupleValueSubst,pairCertSubst,tupleCertSubst,reflSubst,
  rawNumeral,Logic.substNumeral,List.Vector.toList_map]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.NaturalityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.NaturalityProof
