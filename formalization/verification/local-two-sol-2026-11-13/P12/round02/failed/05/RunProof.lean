module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityCertificate.EntryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityCertificate.RunProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRunSplice HistoryKernel.TransitionEquationsProof

theorem internalSingletonRun : Targets.InternalSingletonRun := by
 intro k t old arithmetic x n p I ctx values index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let qline := line I.qtag values
 let cert := certificate I.ctag I.qtag values
 let kt := I.itag+stepTag iterationBase+1
 let count := call (I.ctag+GorbowPRChildTags.argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0)
  (qline ::ᵥ .zero ::ᵥ nil)
 have hk := IdleProof.kernelInstalled p I.itag validity (logical old) arithmetic x I.hi
 obtain ⟨_,_,_,hdisp,_⟩ := HistoryKernel.OptionProof.kernelNodes p kt validity (logical old) arithmetic x hk
 obtain ⟨haccept⟩ := DispatcherProof.internalDispatcher k t old arithmetic x n p I ctx values index fuel .zero
 obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p
  (dispatcherTag kt validity (logical old) arithmetic x) I.dtag 4
  (dispatcher old arithmetic x) hdisp I.hd ctx (index ::ᵥ fuel ::ᵥ .zero ::ᵥ qline ::ᵥ nil)
 obtain ⟨hoption⟩ := HistoryKernel.OptionProof.optionAccepted p kt validity (logical old) arithmetic x hk index fuel .zero qline
 have ho := Derivation.mp hoption (Logic.trans _ _ _ hcopy haccept)
 obtain ⟨hentry⟩ := EntryProof.quotedNewHistory t old arithmetic x p I values
  (someTag kt validity (logical old) arithmetic x) (someInstalled p kt validity (logical old) arithmetic x hk)
 have hs := Logic.unary (.succ (.var 0)) _ _ hentry
 have hout := Logic.trans _ _ _ ho hs
 obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p I.ctag I.hc ctx qline .zero
 obtain ⟨hstep⟩ := ConsRunProof.someCons p I.itag I.ptag I.ctag validity (logical old) arithmetic x
  I.hi I.hp I.hc count .zero qline .zero index fuel
 obtain ⟨hidle⟩ := IdleProof.internalIdle validity (logical old) arithmetic x n p I.itag I.ptag I.hi I.hp ctx count
  (optionValue kt validity (logical old) arithmetic x index fuel .zero qline) index fuel
 have hcount := StationaryProof.iterationCount I.itag cert (.succ count)
  (state I.ptag (.succ .zero) cert) index fuel (.base hcons)
 have hpair := HistoryIteratorSuffix.StepSuffixProof.pairCongruence I.ptag _ .zero _ .zero
  (.base hout) (.base (.logical (.reflexive .zero)))
 exact ⟨Hilbert.Local.finish (localTrans _ _ _ hcount
  (localTrans _ _ _ (.base hstep) (localTrans _ _ _ (.base hidle) hpair)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityCertificate.RunProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityCertificate.RunProof
