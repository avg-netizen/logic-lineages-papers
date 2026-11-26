module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.StatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.OperationalSupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LiteralSyntaxStep.StepSupportProof
theorem iteratorZero {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (state : Term ctx) :
 Computes p G iterator (.zero ::ᵥ state ::ᵥ nil) state := by
 intro tag ht
 have hb := GorbowPRSubtree.Proof.lookupTransport n p tag ⟨2,iterator⟩ 1
  ⟨1,.projection (0 : Fin 1)⟩ ht
  (GorbowPRChildTags.Proof.recursionBase 1 (.projection (0 : Fin 1)) (applyOne tick (.projection 1)))
 obtain ⟨hz⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tag 1
  (.projection (0 : Fin 1)) (applyOne tick (.projection 1)) ht ctx (state ::ᵥ nil)
 obtain ⟨hp⟩ := SixSol20261112.Fuel.Equations.projection p (tag+1) (0 : Fin 1) hb (state ::ᵥ nil)
 exact ⟨.base (Logic.trans _ _ _ hz hp)⟩

theorem lengthZero {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) :
 Computes p G HistoryLengthOffset.lengthProgram ((.zero : Term ctx) ::ᵥ nil) .zero := by
 intro tag ht
 obtain ⟨h⟩ := HistoryLengthOffset.EquationsProof.internalLengthNil n p tag ht ctx
 exact ⟨.base h⟩

theorem emptyAtPair {n ctx : Nat} (p : Program n) (ptag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (tasks : Term ctx) :
 Computes p [] scanCode (tasks ::ᵥ .zero ::ᵥ nil) (.succ tasks) := by
 let args := tasks ::ᵥ .zero ::ᵥ nil
 let state := HistoryKernel.pairCall ptag .zero (.succ tasks)
 have hi : Computes p [] initial args state :=
  binary p [] args HistoryCodec.pair (.projection 1) (applyOne .succ (.projection 0))
   .zero (.succ tasks) state (projection p [] args 1)
   (unary p [] args .succ (.projection 0) tasks (.succ tasks)
    (projection p [] args 0) (successor p [] tasks))
   (copies p [] HistoryCodec.pair ptag hp (.zero ::ᵥ .succ tasks ::ᵥ nil))
 have hl : Computes p [] (applyOne HistoryLengthOffset.lengthProgram (.projection 1)) args .zero :=
  unary p [] args HistoryLengthOffset.lengthProgram (.projection 1) .zero .zero
   (projection p [] args 1) (lengthZero p [])
 have hf : Computes p [] finalState args state :=
  binary p [] args iterator (applyOne HistoryLengthOffset.lengthProgram (.projection 1)) initial
   .zero state state hl hi (iteratorZero p [] state)
 exact unary p [] args (HistoryDecoder.decoder true) finalState state (.succ tasks) hf
  (decoder p [] ptag hp true .zero (.succ tasks))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.OperationalSupportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.OperationalSupportProof
