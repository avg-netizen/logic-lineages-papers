module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.CombinatorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.ConstructorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
variable {n arity ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (args : List.Vector (Term ctx) arity)

theorem addLine (t u : Program arity) (tv uv : Term ctx)
 (hl : Computes p [] t args tv) (hr : Computes p [] u args uv) :
 Computes p [] (RawAddSucc.line t u) args (RawAddSucc.lineCall I.addTag tv uv) := by
 have hz := constantValue p [] args 0
 have hone := constantValue p [] args 1
 have htwo := constantValue p [] args 2
 have hthree := constantValue p [] args 3
 have hcons (q z : Program arity) (v w : Term ctx) (hq : Computes p [] q args v) (hz : Computes p [] z args w) :=
  binary p [] args HistoryCodec.cons q z v w _ hq hz (copies p [] HistoryCodec.cons I.ctag I.hc _)
 have hpair (q z : Program arity) (v w : Term ctx) (hq : Computes p [] q args v) (hz : Computes p [] z args w) :=
  binary p [] args HistoryCodec.pair q z v w _ hq hz (copies p [] HistoryCodec.pair I.ptag I.hp _)
 have happ (q z : Program arity) (v w : Term ctx) (hq : Computes p [] q args v) (hz : Computes p [] z args w) :=
  binary p [] args HistoryAppend.append q z v w _ hq hz (copies p [] HistoryAppend.append I.atag I.ha _)
 have hs := hcons _ _ _ _ htwo hr
 have harg := happ _ _ _ _ hl hs
 have hadd := hcons _ _ _ _ hthree harg
 have hab := happ _ _ _ _ hl hr
 have hsum := hcons _ _ _ _ hthree hab
 have hsucc := hcons _ _ _ _ htwo hsum
 have happ := happ _ _ _ _ hadd hsucc
 have heq := hcons _ _ _ _ hz happ
 have hlast := hcons _ _ _ _ hr hz
 have hargsList := hcons _ _ _ _ hl hlast
 have hrefs := hpair _ _ _ _ hz hz
 have hargs := hpair _ _ _ _ hargsList hrefs
 have hpay := hpair _ _ _ _ hthree hargs
 have hrule := hpair _ _ _ _ hone hpay
 have hconclusion := hpair _ _ _ _ heq hrule
 have hval : Computes p [] (RawAddSucc.line t u) args (RawAddSucc.lineValue I.ptag I.ctag I.atag tv uv) :=
  hpair _ _ _ _ hz hconclusion
 obtain ⟨he⟩ := RawAddSucc.StatementChecks.exactInternalLine n p I.addTag I.ptag I.ctag I.atag I.hadd I.hp I.hc I.ha ctx tv uv
 intro tag htag
 obtain ⟨hv⟩ := hval tag htag
 exact ⟨localTrans _ _ _ hv (.base (Support.equalitySymmetry _ _ he))⟩

theorem computationCompute (t u v cert : Program arity) (tv uv vv cv : Term ctx)
 (ht : Computes p [] t args tv) (hu : Computes p [] u args uv) (hv : Computes p [] v args vv) (hc : Computes p [] cert args cv) :
 Computes p [] (computation t u v cert) args
  (RawAdditionComputation.stepCertificate I.mpTag I.qtag I.replaceTag I.reflexivityTag I.addTag I.ctag I.atag tv uv vv cv) := by
 have hab := CombinatorProof.bin p old a x I args 3 _ _ _ _ ht hu
 have hsu := CombinatorProof.succ p old a x I args _ _ hu
 have hasu := CombinatorProof.bin p old a x I args 3 _ _ _ _ ht hsu
 have hsab := CombinatorProof.succ p old a x I args _ _ hab
 have hsv := CombinatorProof.succ p old a x I args _ _ hv
 have hax := CombinatorProof.single p old a x I args _ _ (addLine p old a x I args _ _ _ _ ht hu)
 have hcg := CombinatorProof.congruenceCompute p old a x I args _ _ _ _ _ _ hab hv hc
 exact CombinatorProof.transitivityCompute p old a x I args _ _ _ _ _ _ _ _ _ _ hasu hsab hsv hax hcg

theorem internalBase : ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (unaryCall I.baseTag t) (RawIteratedSucc.state I.ptag (RawAdditionComputation.zeroRaw I.ctag) t
   (RawCumulativeArithmetic.certificate I.ctag I.zeroTag t))))
def InternalStep : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u v cert : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (binaryCall I.stepTag t (RawIteratedSucc.state I.ptag u v cert))
   (RawIteratedSucc.state I.ptag (RawAdditionComputation.succRaw I.ctag u) (RawAdditionComputation.succRaw I.ctag v)
    (RawAdditionComputation.stepCertificate I.mpTag I.qtag I.replaceTag I.reflexivityTag I.addTag I.ctag I.atag t u v cert)))) := by
 intro n p old a x I ctx t
 let args := t ::ᵥ nil
 have ht := projection p [] args 0
 have hz := constantValue p [] args 0
 have hzero := binary p [] args HistoryCodec.cons _ _ _ _ _ (constantValue p [] args 1) hz
  (copies p [] HistoryCodec.cons I.ctag I.hc _)
 have hl : Computes p [] RawAddZero.lineConstructor args (RawAddZero.lineCall I.zeroTag t) :=
  copies p [] RawAddZero.lineConstructor I.zeroTag I.hzero args
 have hcert := CombinatorProof.single p old a x I args _ _ hl
 have htail := binary p [] args HistoryCodec.pair _ _ _ _ _ ht hcert (copies p [] HistoryCodec.pair I.ptag I.hp _)
 obtain ⟨h⟩ := binary p [] args HistoryCodec.pair _ _ _ _ _ hzero htail (copies p [] HistoryCodec.pair I.ptag I.hp _) I.baseTag I.hbase
 exact ⟨Hilbert.Local.finish h⟩

theorem internalStep : ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u v cert : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (binaryCall I.stepTag t (RawIteratedSucc.state I.ptag u v cert))
   (RawIteratedSucc.state I.ptag (RawAdditionComputation.succRaw I.ctag u) (RawAdditionComputation.succRaw I.ctag v)
    (RawAdditionComputation.stepCertificate I.mpTag I.qtag I.replaceTag I.reflexivityTag I.addTag I.ctag I.atag t u v cert)))) := by
 intro n p old a x I ctx t u v cert
 let args := t ::ᵥ RawIteratedSucc.state I.ptag u v cert ::ᵥ nil
 let tail := HistoryKernel.pairCall I.ptag v cert
 have ht : Computes p [] (.projection 0) args t := projection p [] args 0
 have hs : Computes p [] (.projection 1) args (RawIteratedSucc.state I.ptag u v cert) := projection p [] args 1
 have hu : Computes p [] currentNumeral args u :=
  RawReflexivity.LogicalProof.decoded p [] I.ptag I.hp args (.projection 1) false u tail hs
 have htail := RawReflexivity.LogicalProof.decoded p [] I.ptag I.hp args (.projection 1) true u tail hs
 have hv : Computes p [] currentValue args v :=
  RawReflexivity.LogicalProof.decoded p [] I.ptag I.hp args (applyOne (HistoryDecoder.decoder true) (.projection 1)) false v cert htail
 have hc : Computes p [] currentCertificate args cert :=
  RawReflexivity.LogicalProof.decoded p [] I.ptag I.hp args (applyOne (HistoryDecoder.decoder true) (.projection 1)) true v cert htail
 have hsu := CombinatorProof.succ p old a x I args _ _ hu
 have hsv := CombinatorProof.succ p old a x I args _ _ hv
 have hcert := computationCompute p old a x I args _ _ _ _ _ _ _ _ ht hu hv hc
 have houtTail := binary p [] args HistoryCodec.pair _ _ _ _ _ hsv hcert (copies p [] HistoryCodec.pair I.ptag I.hp _)
 obtain ⟨hout⟩ := binary p [] args HistoryCodec.pair _ _ _ _ _ hsu houtTail (copies p [] HistoryCodec.pair I.ptag I.hp _) I.stepTag I.hstep
 exact ⟨Hilbert.Local.finish hout⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.ConstructorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.ConstructorProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.ConstructorProof.computationCompute
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.ConstructorProof.internalBase
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAdditionIteration.ConstructorProof.internalStep
