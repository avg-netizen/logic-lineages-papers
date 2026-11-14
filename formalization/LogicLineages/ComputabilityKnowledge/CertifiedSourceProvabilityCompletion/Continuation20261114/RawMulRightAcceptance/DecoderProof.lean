module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightAcceptance.SplitProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightAcceptance.DecoderProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open RawMulRightReplace TwoSol20261113.ReflexivityRecognizer
theorem templateCompute {n ctx : Nat} (p : Program n) (old : Program 1) (I : Installation p old)
 (G : List (Formula ctx)) (raw rawB rawV : Term ctx) :
 Computes p G templateCode (lineValue I.pairTag I.consTag I.appendTag raw rawB rawV ::ᵥ nil)
 (templateValue I.consTag I.appendTag raw rawV) := by
 let eq := formulaValue I.consTag I.appendTag raw rawB rawV
 let templ := templateValue I.consTag I.appendTag raw rawV
 let lastArg := HistoryLookup.consCall I.consTag rawB .zero
 let twoArgs := HistoryLookup.consCall I.consTag raw lastArg
 let threeArgs := HistoryLookup.consCall I.consTag templ twoArgs
 let refs := HistoryKernel.pairCall I.pairTag (.zero : Term ctx) .zero
 let pairArgs := HistoryKernel.pairCall I.pairTag threeArgs refs
 let payload := HistoryKernel.pairCall I.pairTag (Term.numeral 12) pairArgs
 let rule := HistoryKernel.pairCall I.pairTag .zero payload
 let conclusion := HistoryKernel.pairCall I.pairTag eq rule
 let outLine := lineValue I.pairTag I.consTag I.appendTag raw rawB rawV
 let args := outLine ::ᵥ nil
 have hline : Computes p G (.projection 0) args (HistoryKernel.pairCall I.pairTag .zero conclusion) := projection p G args 0
 have hconclusion := RawReflexivity.LogicalProof.decoded p G I.pairTag I.hp args (.projection 0) true .zero conclusion hline
 have hrule := RawReflexivity.LogicalProof.decoded p G I.pairTag I.hp args (right (.projection 0)) true eq rule hconclusion
 have hpayload := RawReflexivity.LogicalProof.decoded p G I.pairTag I.hp args (right (right (.projection 0))) true .zero payload hrule
 have hpairArgs := RawReflexivity.LogicalProof.decoded p G I.pairTag I.hp args (right (right (right (.projection 0)))) true (Term.numeral 12) pairArgs hpayload
 have hthree : Computes p G argsCode args threeArgs :=
  RawReflexivity.LogicalProof.decoded p G I.pairTag I.hp args (right (right (right (right (.projection 0))))) false threeArgs refs hpairArgs
 have headOf : Computes p G HistoryLookup.head (threeArgs ::ᵥ nil) templ := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalHeadCons n p tag I.consTag ht I.hc ctx templ twoArgs
  exact ⟨.base h⟩
 exact unary p G args HistoryLookup.head argsCode threeArgs templ hthree headOf

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightAcceptance.DecoderProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightAcceptance.DecoderProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightAcceptance.DecoderProof.templateCompute
