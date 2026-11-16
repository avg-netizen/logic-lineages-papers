module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.GraphSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.TransitivityGraph
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives
theorem transitivityGraph {arity inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : Installation p J)
 (left middle right first second : Program inputs) (lv mv rv fv sv : Term ctx)
 (hl : Computes p left args lv) (hm : Computes p middle args mv) (hr : Computes p right args rv)
 (hf : Computes p first args fv) (hs : Computes p second args sv) :
 Computes p (CurrentRecursionBaseProgram.transitivity left middle right first second) args
  (transitivityCertificate J.mtag J.ctag J.atag J.constructorTag lv mv rv fv sv) := by
 have hmatrix : Computes p (CurrentRecursionBaseProgram.headQuote (.equal (.var 1) (.var 0) : Formula 2) (fun _ => left)) args
  (equalValue J.ctag J.atag lv (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1)))))) := by
  apply headGraph p args (.equal (.var 1) (.var 0) : Formula 2) (fun _ => left) (lv ::ᵥ nil) J.ctag J.atag I.hc I.ha
  intro i
  cases i using Fin.cases with
  | zero => exact hl
  | succ i => exact Fin.elim0 i
 have hleft := GraphSupport.binaryCode p args J I 0 left middle lv mv hl hm
 have hright := GraphSupport.binaryCode p args J I 0 left right lv rv hl hr
 exact mpGraph p args J.mtag I.hm _ _ _ _ _ _ hright
  (mpGraph p args J.mtag I.hm _ _ _ _ _ _
   (GraphSupport.binaryCode p args J I 7 _ _ _ _ hleft hright)
   (replacementGraph p args J.ctag J.constructorTag I.hc I.h12 _ _ _ _ _ _ hmatrix hm hr) hs) hf
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.TransitivityGraph
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.TransitivityGraph
