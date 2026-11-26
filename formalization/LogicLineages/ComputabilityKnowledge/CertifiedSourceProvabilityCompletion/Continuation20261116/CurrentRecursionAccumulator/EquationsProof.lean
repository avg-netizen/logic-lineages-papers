module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.GraphSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.EquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open GorbowPublishedDCB
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115

theorem zero {n m ctx : Nat} (p : Program n) (base : Program m) (formula step : Program (m+1))
 (R : Installation p base formula step) (params : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (familyCall R.producerTag .zero params) (call R.baseTag params))) := by
 have hb := GorbowPRSubtree.Proof.lookupTransport n p R.producerTag ⟨m+1,producer base formula step⟩ 1 ⟨m,base⟩ R.h_producer
  (GorbowPRChildTags.Proof.recursionBase m base (join formula step))
 obtain ⟨hz⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p R.producerTag m base (join formula step) R.h_producer ctx params
 obtain ⟨hc⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p (R.producerTag+1) R.baseTag m base hb R.h_base ctx params
 exact ⟨Logic.trans _ _ _ hz hc⟩

theorem successor {n m ctx : Nat} (p : Program n) (base : Program m) (formula step : Program (m+1))
 (R : Installation p base formula step) (mtag : Nat) (hm : (nodes p)[mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (counter : Term ctx) (params : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (familyCall R.producerTag (.succ counter) params)
   (LiteralMPRun.certificate mtag .zero (familyCall R.formulaTag (.succ counter) params)
    (familyCall R.stepTag counter params) (familyCall R.producerTag counter params)))) := by
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p R.producerTag m base (join formula step) R.h_producer ctx counter params
 obtain ⟨hj⟩ := GraphSupport.joinCall p formula step R.formulaTag R.stepTag mtag R.h_formula R.h_step hm
  counter (familyCall R.producerTag counter params) params (R.producerTag+stepTag base)
  (Equations.recursionStepChild p R.producerTag base (join formula step) R.h_producer)
 exact ⟨Logic.trans _ _ _ hr hj⟩

theorem exactEquations : Targets.InternalEquations := by
 intro installed lhs rhs k t old a baseX pF pR I m base formula step R ctx counter params
 dsimp only
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 have hTU := CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX
 obtain ⟨hz⟩ := zero p base formula step R params
 obtain ⟨hs⟩ := successor p base formula step R I.previous.previous.previous.previous.previous.mpTag
  I.previous.previous.previous.previous.previous.hmp counter params
 obtain ⟨hz⟩ := GorbowTheoryProofProof.monotonicity _ U hTU ctx _ ⟨hz⟩
 obtain ⟨hs⟩ := GorbowTheoryProofProof.monotonicity _ U hTU ctx _ ⟨hs⟩
 exact ⟨.mp (.mp (.logical (.andIntro _ _)) hz) hs⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.EquationsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.EquationsProof
