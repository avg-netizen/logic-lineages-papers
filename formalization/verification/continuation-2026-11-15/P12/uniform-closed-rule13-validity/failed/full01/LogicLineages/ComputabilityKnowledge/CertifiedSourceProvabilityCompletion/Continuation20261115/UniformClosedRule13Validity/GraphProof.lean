module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Validity.ArgumentsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Validity.GraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
noncomputable def binaryCongruence {T : Sentence → Prop} {ctx : Nat} (tag : Nat) (a b c d : Term ctx)
 (ha : Derivation T (.equal a c)) (hb : Derivation T (.equal b d)) :
 Derivation T (.equal (call tag (a ::ᵥ b ::ᵥ nil)) (call tag (c ::ᵥ d ::ᵥ nil))) := by
 apply Logic.callCongruence T tag (a ::ᵥ b ::ᵥ nil) (c ::ᵥ d ::ᵥ nil)
 intro i
 cases i using Fin.cases with
 | zero => exact ha
 | succ i => cases i using Fin.cases with
   | zero => exact hb
   | succ i => exact Fin.elim0 i
/-- No calibration is used: decoded argument equations, installed instance and
case graphs, and predecessor-of-successor produce the exact literal result. -/
theorem exactConclusionGraph : Targets.InternalConclusionGraph := by
 intro n p I ctx f t
 let T := GorbowPRNumeralCalculation.Theory p
 let A := UniformClosedInstanceRecognizer.guards I.fval I.vtag f t
 let G := [A]
 let args := UniformClosedRule13.argumentsValue I.ctag f t
 let result := UniformClosedInstanceRecognizer.outputValue I.ftag I.ptag I.ctag I.rtag f t
 obtain ⟨hfirst⟩ := ArgumentsProof.first p I f t
 obtain ⟨hsecond⟩ := ArgumentsProof.second p I f t
 obtain ⟨hlen⟩ := ArgumentsProof.lengthTwo p I f t
 obtain ⟨hgraph⟩ := UniformClosedInstanceRecognizer.StatementChecks.exactGuardedGraph n p
  I.itag I.ftag I.fval I.vtag I.ptag I.ctag I.rtag I.h_itag I.h_ftag I.h_fval I.h_vtag I.h_ptag I.h_ctag I.h_rtag ctx f t
 have hpos := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) (Hilbert.Local.base (Gamma := G) hgraph)
 have ha : Hilbert.Local T ctx G A := .hypothesis List.mem_cons_self
 have hresult := Hilbert.Local.mp hpos ha
 have hargs := binaryCongruence I.itag _ _ f t hfirst hsecond
 have hinst : Hilbert.Local T ctx G
  (.equal (UniformClosedCase13.instanceValue I.itag I.htag I.ttag args) (.succ result)) :=
  localTrans _ _ _ (.base hargs) hresult
 obtain ⟨hcase⟩ := UniformClosedCase13.BranchProof.accepted p G I.itag I.len I.htag I.ttag I.ctag I.atag
  I.h_itag I.h_len I.h_htag I.h_ttag I.h_ctag I.h_atag args result (.base hlen) hinst I.caseTag I.h_caseTag
 let expanded := UniformClosedCase13.formulaValue I.ctag I.atag (UniformClosedCase13.firstValue I.htag args) result
 have hpredArgs := callCongruence I.predTag
  (UniformClosedCase13.caseCall I.caseTag args ::ᵥ nil) ((.succ expanded) ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact hcase
   | succ i => exact Fin.elim0 i)
 obtain ⟨hpred⟩ := predecessor p G expanded I.predTag I.h_predTag
 have hcompiled := localTrans _ _ _ hpredArgs hpred
 have hquant := binaryCongruence I.ctag (Term.numeral 10) _ (Term.numeral 10) f
  (.logical (.reflexive _)) hfirst
 have happ := binaryCongruence I.atag _ result _ result hquant (.logical (.reflexive _))
 have hshape := binaryCongruence I.ctag (Term.numeral 7) _ (Term.numeral 7) _
  (.logical (.reflexive _)) happ
 have hout := localTrans _ _ _ hcompiled (.base hshape)
 exact ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Validity.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Validity.GraphProof
