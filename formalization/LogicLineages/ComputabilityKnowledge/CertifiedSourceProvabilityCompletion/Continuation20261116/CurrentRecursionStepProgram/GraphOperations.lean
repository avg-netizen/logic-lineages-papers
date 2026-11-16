module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.GraphOperations
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives

theorem binaryGraph {arity inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (ctag atag : Nat) (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (opcode : Nat) (a b : Program inputs) (av bv : Term ctx) (haa : Computes p a args av) (hbb : Computes p b args bv) :
 Computes p (FixedFormulaSubstitution.binary opcode a b) args (FixedFormulaSubstitution.binaryValue ctag atag opcode av bv) :=
 binary p args HistoryCodec.cons ctag hc _ _ _ _ (constantValue p args opcode)
  (binary p args HistoryAppend.append atag ha a b av bv haa hbb)

theorem propositionalGraph {arity inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (ctag ltag : Nat) (isS : Bool) (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hl : (nodes p)[ltag]? = some ⟨3,UniformClosedPropositional.lineConstructor isS⟩)
 (a b c : Program inputs) (av bv cv : Term ctx)
 (ha : Computes p a args av) (hb : Computes p b args bv) (hcc : Computes p c args cv) :
 Computes p (propositional isS a b c) args (UniformClosedPropositionalCertificate.certificate ctag ltag av bv cv) := by
 apply singletonGraph p args ctag hc _ (UniformClosedPropositional.lineCall ltag av bv cv)
 apply CurrentRecursionAccumulator.GraphSupport.composition p args _ ltag hl _ (av ::ᵥ bv ::ᵥ cv ::ᵥ nil)
 intro i
 cases i using Fin.cases with
 | zero => exact ha
 | succ i => cases i using Fin.cases with
   | zero => exact hb
   | succ i => cases i using Fin.cases with
     | zero => exact hcc
     | succ i => exact Fin.elim0 i

theorem liftGraph {arity inputs m ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (base : Program m) (step : Program (m+2)) (child : Program (m+3)) (J : Tags) (I : Installation p base step child J)
 (a b code : Program inputs) (av bv cv : Term ctx)
 (ha : Computes p a args av) (hb : Computes p b args bv) (hcode : Computes p code args cv) :
 Computes p (liftProgram a b code) args (liftValue J av bv cv) :=
 mpGraph p args J.mtag I.hm _ _ _ _ _ _ (binaryGraph p args J.ctag J.atag I.hc I.ha 7 b a bv av hb ha)
  (propositionalGraph p args J.ctag J.ktag false I.hc I.hk a b a av bv av ha hb ha) hcode

theorem mpUnderGraph {arity inputs m ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (base : Program m) (step : Program (m+2)) (child : Program (m+3)) (J : Tags) (I : Installation p base step child J)
 (a b c hi ha : Program inputs) (av bv cv iv hv : Term ctx)
 (hA : Computes p a args av) (hB : Computes p b args bv) (hC : Computes p c args cv)
 (hI : Computes p hi args iv) (hH : Computes p ha args hv) :
 Computes p (mpUnderProgram a b c hi ha) args (mpUnderValue J av bv cv iv hv) := by
 have hpq := binaryGraph p args J.ctag J.atag I.hc I.ha 7 a b av bv hA hB
 have hpr := binaryGraph p args J.ctag J.atag I.hc I.ha 7 a c av cv hA hC
 exact mpGraph p args J.mtag I.hm _ _ _ _ _ _ hpr
  (mpGraph p args J.mtag I.hm _ _ _ _ _ _ (binaryGraph p args J.ctag J.atag I.hc I.ha 7 _ _ _ _ hpq hpr)
   (propositionalGraph p args J.ctag J.stag true I.hc I.hs a b c av bv cv hA hB hC) hI) hH

theorem reflexivityGraph {arity inputs m ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (base : Program m) (step : Program (m+2)) (child : Program (m+3)) (J : Tags) (I : Installation p base step child J)
 (raw : Program inputs) (rv : Term ctx) (hr : Computes p raw args rv) :
 Computes p (reflexivity raw) args (RawCumulativeLogical.certificate J.ctag J.reflexivityTag rv) :=
 singletonGraph p args J.ctag I.hc _ _ (unary p args RawReflexivity.lineConstructor J.reflexivityTag I.hr raw rv hr)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.GraphOperations
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.GraphOperations
