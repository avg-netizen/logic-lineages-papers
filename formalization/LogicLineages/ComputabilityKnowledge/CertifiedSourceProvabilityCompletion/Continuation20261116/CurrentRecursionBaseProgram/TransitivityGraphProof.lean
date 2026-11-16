module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.GraphPrimitives
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.TransitivityGraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open GraphPrimitives

theorem binaryGraph {arity inputs m ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (base : Program m) (child : Program (m+1)) (J : Tags) (I : Installation p base child J)
 (opcode : Nat) (a b : Program inputs) (av bv : Term ctx) (ha : Computes p a args av) (hb : Computes p b args bv) :
 Computes p (FixedFormulaSubstitution.binary opcode a b) args (FixedFormulaSubstitution.binaryValue J.ctag J.atag opcode av bv) :=
 binary p args HistoryCodec.cons J.ctag I.hc _ _ _ _ (constantValue p args opcode)
  (binary p args HistoryAppend.append J.atag I.ha a b av bv ha hb)

theorem transitivityGraph {arity inputs m ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (base : Program m) (child : Program (m+1)) (J : Tags) (I : Installation p base child J)
 (left middle right first second : Program inputs) (lv mv rv fv sv : Term ctx)
 (hl : Computes p left args lv) (hm : Computes p middle args mv) (hr : Computes p right args rv)
 (hf : Computes p first args fv) (hs : Computes p second args sv) :
 Computes p (transitivity left middle right first second) args
  (transitivityCertificate J.mtag J.ctag J.atag J.r12 lv mv rv fv sv) := by
 have hmatrix : Computes p (headQuote (.equal (.var 1) (.var 0) : Formula 2) (fun _ => left)) args
  (equalValue J.ctag J.atag lv (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1)))))) := by
  apply headGraph p args (.equal (.var 1) (.var 0) : Formula 2) (fun _ => left) (lv ::ᵥ nil) J.ctag J.atag I.hc I.ha
  intro i
  cases i using Fin.cases with
  | zero => exact hl
  | succ i => exact Fin.elim0 i
 have hleft := binaryGraph p args base child J I 0 left middle lv mv hl hm
 have hright := binaryGraph p args base child J I 0 left right lv rv hl hr
 exact mpGraph p args J.mtag I.hm _ _ _ _ _ _ hright
  (mpGraph p args J.mtag I.hm _ _ _ _ _ _
   (binaryGraph p args base child J I 7 _ _ _ _ hleft hright)
   (replacementGraph p args J.ctag J.r12 I.hc I.h12 _ _ _ _ _ _ hmatrix hm hr) hs) hf
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.TransitivityGraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.TransitivityGraphProof
