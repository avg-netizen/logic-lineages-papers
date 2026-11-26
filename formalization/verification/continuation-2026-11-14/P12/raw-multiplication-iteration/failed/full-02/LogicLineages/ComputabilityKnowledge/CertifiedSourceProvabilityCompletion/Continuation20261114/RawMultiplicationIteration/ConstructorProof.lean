module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.CombinatorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.ConstructorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
variable {n arity ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (args : List.Vector (Term ctx) arity)
theorem internalBase : Targets.InternalBase := by
 intro n p old a x I ctx m
 let args := m ::ᵥ nil
 have hm := projection p [] args 0
 have hz := constantValue p [] args 0
 have hzero := binary p [] args HistoryCodec.cons _ _ _ _ _ (constantValue p [] args 1) hz
  (copies p [] HistoryCodec.cons I.ctag I.hc _)
 have hnum := CombinatorProof.numeral p old a x I args _ _ hm
 have hl := unary p [] args RawMultiplication.Zero.lineConstructor _ _ _ hnum
  (copies p [] RawMultiplication.Zero.lineConstructor I.mulZeroTag I.hmulZero _)
 have hcert := RawRetainedAdditionIteration.CombinatorProof.single p old a x I.toComputation.toEvaluator args _ _ hl
 have htail := binary p [] args HistoryCodec.pair _ _ _ _ _ hz hcert (copies p [] HistoryCodec.pair I.ptag I.hp _)
 obtain ⟨h⟩ := binary p [] args HistoryCodec.pair _ _ _ _ _ hzero htail (copies p [] HistoryCodec.pair I.ptag I.hp _) I.mulBaseTag I.hmulBase
 exact ⟨Hilbert.Local.finish h⟩

theorem internalStep : Targets.InternalStep := by
 intro n p old a x I ctx m u z cert
 let args := m ::ᵥ RawIteratedSucc.state I.ptag u z cert ::ᵥ nil
 let tail := HistoryKernel.pairCall I.ptag z cert
 have hm : Computes p [] (.projection 0) args m := projection p [] args 0
 have hs : Computes p [] (.projection 1) args (RawIteratedSucc.state I.ptag u z cert) := projection p [] args 1
 have hu : Computes p [] rightRaw args u :=
  RawReflexivity.LogicalProof.decoded p [] I.ptag I.hp args (.projection 1) false u tail hs
 have htail := RawReflexivity.LogicalProof.decoded p [] I.ptag I.hp args (.projection 1) true u tail hs
 have hz : Computes p [] value args z :=
  RawReflexivity.LogicalProof.decoded p [] I.ptag I.hp args (applyOne (HistoryDecoder.decoder true) (.projection 1)) false z cert htail
 have hc : Computes p [] certificateRaw args cert :=
  RawReflexivity.LogicalProof.decoded p [] I.ptag I.hp args (applyOne (HistoryDecoder.decoder true) (.projection 1)) true z cert htail
 have hsu := RawRetainedAdditionIteration.CombinatorProof.succ p old a x I.toComputation.toEvaluator args _ _ hu
 have hn := CombinatorProof.next p args _ _ _ _ hm hz
 have hcert := CombinatorProof.computationCompute p old a x I args _ _ _ _ _ _ _ _ hm hu hz hc
 have houtTail := binary p [] args HistoryCodec.pair _ _ _ _ _ hn hcert (copies p [] HistoryCodec.pair I.ptag I.hp _)
 obtain ⟨hout⟩ := binary p [] args HistoryCodec.pair _ _ _ _ _ hsu houtTail (copies p [] HistoryCodec.pair I.ptag I.hp _) I.mulStepTag I.hmulStep
 exact ⟨Hilbert.Local.finish hout⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.ConstructorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.ConstructorProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.ConstructorProof.internalBase
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.ConstructorProof.internalStep
