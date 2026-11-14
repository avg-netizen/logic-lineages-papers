module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccIteration.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccIteration.StepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem internalStep : Targets.InternalStep := by
 intro n p old a x I ctx t u cert
 let args := state I.ptag t u cert ::ᵥ nil
 let tail := HistoryKernel.pairCall I.ptag u cert
 have hs : Computes p [] (.projection 0) args (state I.ptag t u cert) := projection p [] args 0
 have ht : Computes p [] leftRaw args t :=
  RawReflexivity.LogicalProof.decoded p [] I.ptag I.hp args (.projection 0) false t tail hs
 have htail := RawReflexivity.LogicalProof.decoded p [] I.ptag I.hp args (.projection 0) true t tail hs
 have hu : Computes p [] rightRaw args u :=
  RawReflexivity.LogicalProof.decoded p [] I.ptag I.hp args (applyOne (HistoryDecoder.decoder true) (.projection 0)) false u cert htail
 have hcert : Computes p [] inputCertificate args cert :=
  RawReflexivity.LogicalProof.decoded p [] I.ptag I.hp args (applyOne (HistoryDecoder.decoder true) (.projection 0)) true u cert htail
 have hz := constantValue p [] args 0
 have htwo := constantValue p [] args 2
 have hcons (v w : Term ctx) := copies p [] HistoryCodec.cons I.ctag I.hc (v ::ᵥ w ::ᵥ nil)
 have hpair (v w : Term ctx) := copies p [] HistoryCodec.pair I.ptag I.hp (v ::ᵥ w ::ᵥ nil)
 have st : Computes p [] (RawAddSucc.successorRaw leftRaw) args (RawSuccReplace.succValue I.ctag t) :=
  binary p [] args HistoryCodec.cons _ _ _ _ _ htwo ht (hcons _ _)
 have su : Computes p [] (RawAddSucc.successorRaw rightRaw) args (RawSuccReplace.succValue I.ctag u) :=
  binary p [] args HistoryCodec.cons _ _ _ _ _ htwo hu (hcons _ _)
 have bin (token : Nat) (q z : Program 1) (v w : Term ctx)
  (hq : Computes p [] q args v) (hz : Computes p [] z args w) :
  Computes p [] (RawSuccReplace.binaryRaw token q z) args (RawSuccReplace.binaryValue I.ctag I.atag token v w) := by
  have happ := binary p [] args HistoryAppend.append _ _ _ _ _ hq hz
   (copies p [] HistoryAppend.append I.atag I.ha (v ::ᵥ w ::ᵥ nil))
  exact binary p [] args HistoryCodec.cons _ _ _ _ _ (constantValue p [] args token) happ (hcons _ _)
 have houtRaw : Computes p [] outputRaw args (RawSuccCongruence.outputRaw I.ctag I.atag t u) := bin 0 _ _ _ _ st su
 have hselfRaw : Computes p [] selfRaw args (RawSuccCongruence.selfRaw I.ctag I.atag t) := bin 0 _ _ _ _ st st
 have hintermediate : Computes p [] intermediateRaw args (RawSuccCongruence.intermediateRaw I.ctag I.atag t u) := bin 7 _ _ _ _ hselfRaw houtRaw
 have hreplaceValue := RawSuccReplace.ConstructorProof.computesLine p [] I.ptag I.ctag I.atag I.hp I.hc I.ha args leftRaw rightRaw t u ht hu
 obtain ⟨hrEq⟩ := RawSuccReplace.StatementChecks.exactInternalLine n p I.replaceTag I.ptag I.ctag I.atag I.hreplace I.hp I.hc I.ha ctx t u
 have hreplace : Computes p [] (RawSuccReplace.line leftRaw rightRaw) args (RawSuccReplace.lineCall I.replaceTag t u) := by
  intro tag htag
  obtain ⟨h⟩ := hreplaceValue tag htag
  exact ⟨localTrans _ _ _ h (.base (Support.equalitySymmetry _ _ hrEq))⟩
 have hreplaceCert : Computes p [] replacementCertificate args (RawSuccReplaceCertificate.certificate I.ctag I.replaceTag t u) :=
  binary p [] args HistoryCodec.cons _ _ _ _ _ hreplace hz (hcons _ _)
 let succT := RawSuccReplace.succValue I.ctag t
 have happ := binary p [] args HistoryAppend.append _ _ _ _ _ st st
  (copies p [] HistoryAppend.append I.atag I.ha (succT ::ᵥ succT ::ᵥ nil))
 have heq := binary p [] args HistoryCodec.cons _ _ _ _ _ hz happ (hcons _ _)
 have hsingle := binary p [] args HistoryCodec.cons _ _ _ _ _ st hz (hcons _ _)
 have hrefs := binary p [] args HistoryCodec.pair _ _ _ _ _ hz hz (hpair _ _)
 have hargs := binary p [] args HistoryCodec.pair _ _ _ _ _ hsingle hrefs (hpair _ _)
 have hpay := binary p [] args HistoryCodec.pair _ _ _ _ _ (constantValue p [] args 11) hargs (hpair _ _)
 have hrule := binary p [] args HistoryCodec.pair _ _ _ _ _ hz hpay (hpair _ _)
 have hconcl := binary p [] args HistoryCodec.pair _ _ _ _ _ heq hrule (hpair _ _)
 have hlineValue : Computes p [] (TwoSol20261113.ReflexivityRecognizer.reflexiveLine (RawAddSucc.successorRaw leftRaw)) args
  (RawReflexivity.lineValue I.ptag I.ctag I.atag succT) :=
  binary p [] args HistoryCodec.pair _ _ _ _ _ hz hconcl (hpair _ _)
 obtain ⟨hrefEq⟩ := RawReflexivity.StatementChecks.exactInternalLine n p I.reflexivityTag I.ptag I.ctag I.atag I.hreflexivity I.hp I.hc I.ha ctx succT
 have hlineRef : Computes p [] (TwoSol20261113.ReflexivityRecognizer.reflexiveLine (RawAddSucc.successorRaw leftRaw)) args
  (RawReflexivity.lineCall I.reflexivityTag succT) := by
  intro tag htag
  obtain ⟨h⟩ := hlineValue tag htag
  exact ⟨localTrans _ _ _ h (.base (Support.equalitySymmetry _ _ hrefEq))⟩
 have hrefCert : Computes p [] reflexivityCertificate args (RawCumulativeLogical.certificate I.ctag I.reflexivityTag succT) :=
  binary p [] args HistoryCodec.cons _ _ _ _ _ hlineRef hz (hcons _ _)
 have hmp (q i j : Program 1) (v w z : Term ctx)
  (hq : Computes p [] q args v) (hi : Computes p [] i args w) (hj : Computes p [] j args z) :
  Computes p [] (mp q i j) args (LiteralMPRun.certificate I.mpTag .zero v w z) := by
  apply compose p [] LiteralRawMP.constructor
   (Fin.cases (constant 1 0) (Fin.cases q (Fin.cases i (Fin.cases j Fin.elim0))))
   args (.zero ::ᵥ v ::ᵥ w ::ᵥ z ::ᵥ nil) _
  · intro k
    cases k using Fin.cases with
    | zero => exact hz
    | succ k => cases k using Fin.cases with
      | zero => exact hq
      | succ k => cases k using Fin.cases with
        | zero => exact hi
        | succ k => cases k using Fin.cases with
          | zero => exact hj
          | succ k => exact Fin.elim0 k
  · exact copies p [] LiteralRawMP.constructor I.mpTag I.hmp _
 have hfirst := hmp _ _ _ _ _ _ hintermediate hreplaceCert hcert
 have hfinal : Computes p [] outputCertificate args (RawSuccCongruence.certificate I.mpTag I.replaceTag I.reflexivityTag I.ctag I.atag t u cert) :=
  hmp _ _ _ _ _ _ houtRaw hfirst hrefCert
 have htailOut := binary p [] args HistoryCodec.pair _ _ _ _ _ su hfinal (hpair _ _)
 obtain ⟨hout⟩ := binary p [] args HistoryCodec.pair _ _ _ _ _ st htailOut (hpair _ _) I.stepTag I.hstep
 exact ⟨Hilbert.Local.finish hout⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccIteration.StepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccIteration.StepProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccIteration.StepProof.internalStep
