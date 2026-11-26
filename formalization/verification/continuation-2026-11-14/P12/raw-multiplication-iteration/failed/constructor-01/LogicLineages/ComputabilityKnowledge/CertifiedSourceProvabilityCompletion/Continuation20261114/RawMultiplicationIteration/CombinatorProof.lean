module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.CombinatorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
variable {n arity ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (args : List.Vector (Term ctx) arity)
theorem mulLine (t u : Program arity) (tv uv : Term ctx)
 (hl : Computes p [] t args tv) (hr : Computes p [] u args uv) :
 Computes p [] (RawMultiplication.Succ.line t u) args (RawMultiplication.Succ.lineCall I.mulSuccTag tv uv) := by
 have hz := constantValue p [] args 0
 have hone := constantValue p [] args 1
 have htwo := constantValue p [] args 2
 have hthree := constantValue p [] args 3
 have hfour := constantValue p [] args 4
 have hfive := constantValue p [] args 5
 have hcons (q z : Program arity) (v w : Term ctx) (hq : Computes p [] q args v) (hz : Computes p [] z args w) :=
  binary p [] args HistoryCodec.cons q z v w _ hq hz (copies p [] HistoryCodec.cons I.ctag I.hc _)
 have hpair (q z : Program arity) (v w : Term ctx) (hq : Computes p [] q args v) (hz : Computes p [] z args w) :=
  binary p [] args HistoryCodec.pair q z v w _ hq hz (copies p [] HistoryCodec.pair I.ptag I.hp _)
 have happ (q z : Program arity) (v w : Term ctx) (hq : Computes p [] q args v) (hz : Computes p [] z args w) :=
  binary p [] args HistoryAppend.append q z v w _ hq hz (copies p [] HistoryAppend.append I.atag I.ha _)
 have hs := hcons _ _ _ _ htwo hr
 have harg := happ _ _ _ _ hl hs
 have hadd := hcons _ _ _ _ hfour harg
 have hab := happ _ _ _ _ hl hr
 have hsum := hcons _ _ _ _ hfour hab
 have hsumArg := happ _ _ _ _ hsum hl
 have hsucc := hcons _ _ _ _ hthree hsumArg
 have happ := happ _ _ _ _ hadd hsucc
 have heq := hcons _ _ _ _ hz happ
 have hlast := hcons _ _ _ _ hr hz
 have hargsList := hcons _ _ _ _ hl hlast
 have hrefs := hpair _ _ _ _ hz hz
 have hargs := hpair _ _ _ _ hargsList hrefs
 have hpay := hpair _ _ _ _ hfive hargs
 have hrule := hpair _ _ _ _ hone hpay
 have hconclusion := hpair _ _ _ _ heq hrule
 have hval : Computes p [] (RawMultiplication.Succ.line t u) args (RawMultiplication.Succ.lineValue I.ptag I.ctag I.atag tv uv) :=
  hpair _ _ _ _ hz hconclusion
 obtain ⟨he⟩ := RawMultiplication.StatementChecks.exactSuccInternalLine n p I.mulSuccTag I.ptag I.ctag I.atag I.hmulSucc I.hp I.hc I.ha ctx tv uv
 intro tag htag
 obtain ⟨hv⟩ := hval tag htag
 exact ⟨localTrans _ _ _ hv (.base (Support.equalitySymmetry _ _ he))⟩

theorem numeral (m : Program arity) (mv : Term ctx) (hm : Computes p [] m args mv) :
 Computes p [] (applyOne LiteralNumeralPrefix.numeralCode m) args (LiteralNumeralPrefix.numeralCall I.numeralTag mv) :=
 unary p [] args LiteralNumeralPrefix.numeralCode m mv _ hm
  (copies p [] LiteralNumeralPrefix.numeralCode I.numeralTag I.hnumeral _)
theorem next (m z : Program arity) (mv zv : Term ctx)
 (hm : Computes p [] m args mv) (hz : Computes p [] z args zv) :
 Computes p [] (nextValue m z) args (.add zv mv) := by
 apply binary p [] args HistoryCodec.add m z mv zv (.add zv mv) hm hz
 intro tag ht
 obtain ⟨h⟩ := HistoryCodec.StatementChecks.internalAdd n p tag ht ctx mv zv
 exact ⟨.base h⟩
theorem third (q : Program arity) (v : Term ctx) (hq : Computes p [] q args v) :
 Computes p [] (thirdRaw q) args (RawIteratedSucc.third I.rightTag v) := by
 have hr := unary p [] args (HistoryDecoder.decoder true) q v _ hq
  (copies p [] (HistoryDecoder.decoder true) I.rightTag I.hright _)
 exact unary p [] args (HistoryDecoder.decoder true) _ _ _ hr
  (copies p [] (HistoryDecoder.decoder true) I.rightTag I.hright _)

theorem computationCompute (m u z cert : Program arity) (mv uv zv cv : Term ctx)
 (hm : Computes p [] m args mv) (hu : Computes p [] u args uv)
 (hz : Computes p [] z args zv) (hc : Computes p [] cert args cv) :
 Computes p [] (computation m u z cert) args
  (RawMultiplicationComputation.stepCertificate I.mpTag I.qtag I.reflexivityTag I.mulSuccTag I.iteratorTag
   I.congruenceIteratorTag I.numeralTag I.prefixTag I.ptag I.ctag I.atag I.rightTag mv uv zv cv) := by
 let J := I.toComputation.toEvaluator
 have ht := numeral p old a x I args m mv hm
 have hv := numeral p old a x I args z zv hz
 have hn := next p old a x I args m z mv zv hm hz
 have hans := numeral p old a x I args _ _ hn
 have hprod := RawRetainedAdditionIteration.CombinatorProof.bin p old a x J args 4 _ _ _ _ ht hu
 have hsucc := RawRetainedAdditionIteration.CombinatorProof.succ p old a x J args _ _ hu
 have hnext := RawRetainedAdditionIteration.CombinatorProof.bin p old a x J args 4 _ _ _ _ ht hsucc
 have hsum := RawRetainedAdditionIteration.CombinatorProof.bin p old a x J args 3 _ _ _ _ hprod ht
 have hax := RawRetainedAdditionIteration.CombinatorProof.single p old a x J args _ _ (mulLine p old a x I args _ _ _ _ ht hu)
 have hpref := binary p [] args RawAdditionIteration.successorPrefix _ _ _ _ _ hm hprod
  (copies p [] RawAdditionIteration.successorPrefix I.prefixTag I.hprefix _)
 have hadd := binary p [] args RawAdditionIteration.iterator _ _ _ _ _ hm hprod
  (copies p [] RawAdditionIteration.iterator I.iteratorTag I.hiterator _)
 have haddCert := third p old a x I args _ _ hadd
 have htail := binary p [] args HistoryCodec.pair _ _ _ _ _ hv hc (copies p [] HistoryCodec.pair I.ptag I.hp _)
 have hstate := binary p [] args HistoryCodec.pair _ _ _ _ _ hprod htail (copies p [] HistoryCodec.pair I.ptag I.hp _)
 have hcon := binary p [] args RawIteratedSucc.iterator _ _ _ _ _ hm hstate
  (copies p [] RawIteratedSucc.iterator I.congruenceIteratorTag I.hcongruenceIterator _)
 have hconCert := third p old a x I args _ _ hcon
 have hinner := RawRetainedAdditionIteration.CombinatorProof.transitivityCompute p old a x J args _ _ _ _ _ _ _ _ _ _ hsum hpref hans haddCert hconCert
 exact RawRetainedAdditionIteration.CombinatorProof.transitivityCompute p old a x J args _ _ _ _ _ _ _ _ _ _ hnext hsum hans hax hinner
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.CombinatorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.CombinatorProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.CombinatorProof.computationCompute
