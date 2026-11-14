module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawArithmeticCoreRetention.DispatcherProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawArithmeticCoreRetention.RunProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix TwoSol20261113.ReflexivityCertificate
open SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRunSplice HistoryKernel.TransitionEquationsProof
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
theorem newHistory {n ctx : Nat} (p : Program n) (logical old : Program 1) (x : Program 3)
 (I : Installation p logical old x) (formula payload ann index fuel : Term ctx) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨3,HistoryKernel.someExtendedHistory⟩) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryKernel.EntryProof.newHistory tag .zero (line I.ptag formula payload ann))
   (HistoryLookup.consCall I.ctag (HistoryKernel.pairCall I.ptag .zero formula) .zero))) := by
 exact TwoSol20261113.ReflexivityCertificate.EntryProof.newHistoryExact p tag I.ptag I.ctag
  ht I.hp I.hc .zero .zero formula
  (HistoryKernel.pairCall I.ptag (.succ .zero) (HistoryKernel.pairCall I.ptag payload
   (HistoryKernel.pairCall I.ptag ann (HistoryKernel.pairCall I.ptag .zero .zero))))

theorem singletonRun {n ctx : Nat} (p : Program n) (logical old : Program 1) (x : Program 3)
 (I : Installation p logical old x) (formula payload ann index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (LiteralSyntaxValidator.formulaCall I.ftag .zero formula) (.succ .zero))
   (.imp (.equal (leafCall I.oldTag (line I.ptag formula payload ann)) (.succ .zero))
    (.equal (LiteralCheckerAcceptance.runCall I.itag I.ptag index fuel (certificate I.ptag I.ctag formula payload ann))
     (LiteralCheckerAuxiliaries.successfulState I.ptag I.ctag .zero formula .zero .zero))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := Formula.equal (LiteralSyntaxValidator.formulaCall I.ftag .zero formula) (.succ .zero)
 let K := Formula.equal (leafCall I.oldTag (line I.ptag formula payload ann)) (.succ .zero)
 let G := [K,H]
 have hh : Hilbert.Local T ctx G H := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hkValid : Hilbert.Local T ctx G K := .hypothesis List.mem_cons_self
 let qline := line I.ptag formula payload ann
 let cert := certificate I.ptag I.ctag formula payload ann
 let kt := I.itag+stepTag iterationBase+1
 let count := call (I.ctag+GorbowPRChildTags.argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0)
  (qline ::ᵥ .zero ::ᵥ nil)
 have hk := IdleProof.kernelInstalled p I.itag LiteralSyntaxValidator.lineValidator logical (RawMultiplication.arithmeticLeaf old) x I.hi
 obtain ⟨_,_,_,hdisp,_⟩ := HistoryKernel.OptionProof.kernelNodes p kt LiteralSyntaxValidator.lineValidator logical (RawMultiplication.arithmeticLeaf old) x hk
 obtain ⟨haccept⟩ := DispatcherProof.dispatcher p logical old x I formula payload ann index fuel .zero
 obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p
  (dispatcherTag kt LiteralSyntaxValidator.lineValidator logical (RawMultiplication.arithmeticLeaf old) x) I.dtag 4
  (RawMultiplicationCertificates.ZeroDispatcher.dispatcher logical old x) hdisp I.hd ctx (index ::ᵥ fuel ::ᵥ .zero ::ᵥ qline ::ᵥ nil)
 obtain ⟨hoption⟩ := HistoryKernel.OptionProof.optionAccepted p kt LiteralSyntaxValidator.lineValidator logical (RawMultiplication.arithmeticLeaf old) x hk index fuel .zero qline
 have ho := Hilbert.Local.mp (.base hoption)
  (localTrans _ _ _ (.base hcopy) (.mp (.mp (.base haccept) hh) hkValid))
 obtain ⟨hentry⟩ := newHistory p logical old x I formula payload ann index fuel
  (someTag kt LiteralSyntaxValidator.lineValidator logical (RawMultiplication.arithmeticLeaf old) x) (someInstalled p kt LiteralSyntaxValidator.lineValidator logical (RawMultiplication.arithmeticLeaf old) x hk)
 have hs := Logic.unary (.succ (.var 0)) _ _ hentry
 have hout := localTrans _ _ _ ho (.base hs)
 obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p I.ctag I.hc ctx qline .zero
 obtain ⟨hstep⟩ := ConsRunProof.someCons p I.itag I.ptag I.ctag LiteralSyntaxValidator.lineValidator logical (RawMultiplication.arithmeticLeaf old) x
  I.hi I.hp I.hc count .zero qline .zero index fuel
 obtain ⟨hidle⟩ := IdleProof.internalIdle LiteralSyntaxValidator.lineValidator logical (RawMultiplication.arithmeticLeaf old) x n p I.itag I.ptag I.hi I.hp ctx count
  (optionValue kt LiteralSyntaxValidator.lineValidator logical (RawMultiplication.arithmeticLeaf old) x index fuel .zero qline) index fuel
 have hcount := StationaryProof.iterationCount (T := T) (G := G) I.itag cert (.succ count)
  (state I.ptag (.succ .zero) cert) index fuel (.base hcons)
 have hpair := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := G) I.ptag _ .zero _ .zero
  hout (.base (.logical (.reflexive .zero)))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (localTrans _ _ _ hcount
  (localTrans _ _ _ (.base hstep) (localTrans _ _ _ (.base hidle) hpair)))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawArithmeticCoreRetention.RunProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawArithmeticCoreRetention.RunProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawArithmeticCoreRetention.RunProof.newHistory
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawArithmeticCoreRetention.RunProof.singletonRun
