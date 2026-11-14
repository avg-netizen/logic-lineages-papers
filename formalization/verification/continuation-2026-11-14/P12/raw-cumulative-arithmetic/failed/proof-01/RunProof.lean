module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeArithmetic.EntryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeArithmetic.RunProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix TwoSol20261113.ReflexivityCertificate
open SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRunSplice HistoryKernel.TransitionEquationsProof

theorem internalSingletonRun : Targets.InternalSingletonRun := by
 intro n p logical old x I ctx raw index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid I.vtag raw
 let G := [H]
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 let qline := RawAddZero.lineCall I.qtag raw
 let cert := RawCumulativeArithmetic.certificate I.ctag I.qtag raw
 let kt := I.itag+stepTag iterationBase+1
 let count := call (I.ctag+GorbowPRChildTags.argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0)
  (qline ::ᵥ .zero ::ᵥ nil)
 have hk := IdleProof.kernelInstalled p I.itag LiteralSyntaxValidator.lineValidator logical (arithmetic old) x I.hi
 obtain ⟨_,_,_,hdisp,_⟩ := HistoryKernel.OptionProof.kernelNodes p kt LiteralSyntaxValidator.lineValidator logical (arithmetic old) x hk
 obtain ⟨haccept⟩ := DispatcherProof.internalDispatcher n p logical old x
  I.toInstallation ctx raw index fuel .zero
 obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p
  (dispatcherTag kt LiteralSyntaxValidator.lineValidator logical (arithmetic old) x) I.dtag 4
  (dispatcher logical old x) hdisp I.hd ctx (index ::ᵥ fuel ::ᵥ .zero ::ᵥ qline ::ᵥ nil)
 obtain ⟨hoption⟩ := HistoryKernel.OptionProof.optionAccepted p kt LiteralSyntaxValidator.lineValidator logical (arithmetic old) x hk index fuel .zero qline
 have ho := Hilbert.Local.mp (.base hoption)
  (localTrans _ _ _ (.base hcopy) (.mp (.base haccept) hh))
 obtain ⟨hentry⟩ := EntryProof.rawNewHistory p logical old x I raw
  (someTag kt LiteralSyntaxValidator.lineValidator logical (arithmetic old) x) (someInstalled p kt LiteralSyntaxValidator.lineValidator logical (arithmetic old) x hk)
 have hs := Logic.unary (.succ (.var 0)) _ _ hentry
 have hout := localTrans _ _ _ ho (.base hs)
 obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p I.ctag I.hc ctx qline .zero
 obtain ⟨hstep⟩ := ConsRunProof.someCons p I.itag I.ptag I.ctag LiteralSyntaxValidator.lineValidator logical (arithmetic old) x
  I.hi I.hp I.hc count .zero qline .zero index fuel
 obtain ⟨hidle⟩ := IdleProof.internalIdle LiteralSyntaxValidator.lineValidator logical (arithmetic old) x n p I.itag I.ptag I.hi I.hp ctx count
  (optionValue kt LiteralSyntaxValidator.lineValidator logical (arithmetic old) x index fuel .zero qline) index fuel
 have hcount := StationaryProof.iterationCount (T := T) (G := G) I.itag cert (.succ count)
  (state I.ptag (.succ .zero) cert) index fuel (.base hcons)
 have hpair := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := G) I.ptag _ .zero _ .zero
  hout (.base (.logical (.reflexive .zero)))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ hcount
  (localTrans _ _ _ (.base hstep) (localTrans _ _ _ (.base hidle) hpair))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeArithmetic.RunProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeArithmetic.RunProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeArithmetic.RunProof.internalSingletonRun
