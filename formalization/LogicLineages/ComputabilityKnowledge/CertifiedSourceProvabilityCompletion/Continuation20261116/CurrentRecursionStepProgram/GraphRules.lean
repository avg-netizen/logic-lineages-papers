module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.GraphOperations
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.GraphRules
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives
open GraphOperations

theorem unaryGraph {arity inputs m ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (base : Program m) (step : Program (m+2)) (child : Program (m+3)) (J : Tags) (I : Installation p base step child J)
 (openCode t u ft fu : Program inputs) (ov tv uv fv gv : Term ctx)
 (ho : Computes p openCode args ov) (ht : Computes p t args tv) (hu : Computes p u args uv)
 (hf : Computes p ft args fv) (hg : Computes p fu args gv) :
 Computes p (unaryRule openCode t u ft fu) args (unaryValue J ov tv uv fv gv) := by
 have hP := binaryGraph p args J.ctag J.atag I.hc I.ha 0 t u tv uv ht hu
 have hQ := binaryGraph p args J.ctag J.atag I.hc I.ha 0 ft ft fv fv hf hf
 have hR := binaryGraph p args J.ctag J.atag I.hc I.ha 0 ft fu fv gv hf hg
 have hm := binaryGraph p args J.ctag J.atag I.hc I.ha 0 ft openCode fv ov hf ho
 exact mpUnderGraph p args base step child J I _ _ _ _ _ _ _ _ _ _ hP hQ hR
  (replacementGraph p args J.ctag J.r12 I.hc I.h12 _ _ _ _ _ _ hm ht hu)
  (liftGraph p args base step child J I _ _ _ _ _ _ hQ hP (reflexivityGraph p args base step child J I ft fv hf))

theorem transitivityGraph {arity inputs m ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (base : Program m) (step : Program (m+2)) (child : Program (m+3)) (J : Tags) (I : Installation p base step child J)
 (P left middle right hleft hright : Program inputs) (pv lv mv rv hv kv : Term ctx)
 (hP : Computes p P args pv) (hl : Computes p left args lv) (hm : Computes p middle args mv)
 (hr : Computes p right args rv) (hh : Computes p hleft args hv) (hk : Computes p hright args kv) :
 Computes p (transitivityUnder P left middle right hleft hright) args (transitivityValue J pv lv mv rv hv kv) := by
 have hTU := binaryGraph p args J.ctag J.atag I.hc I.ha 0 left middle lv mv hl hm
 have hUV := binaryGraph p args J.ctag J.atag I.hc I.ha 0 middle right mv rv hm hr
 have hTV := binaryGraph p args J.ctag J.atag I.hc I.ha 0 left right lv rv hl hr
 have hmatrix : Computes p (CurrentRecursionBaseProgram.headQuote (.equal (.var 1) (.var 0) : Formula 2) (fun _ => left)) args
  (equalValue J.ctag J.atag lv (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1)))))) := by
  apply headGraph p args (.equal (.var 1) (.var 0) : Formula 2) (fun _ => left) (lv ::ᵥ nil) J.ctag J.atag I.hc I.ha
  intro i
  cases i using Fin.cases with
  | zero => exact hl
  | succ i => exact Fin.elim0 i
 have hseed := replacementGraph p args J.ctag J.r12 I.hc I.h12 _ _ _ _ _ _ hmatrix hm hr
 have hinner := binaryGraph p args J.ctag J.atag I.hc I.ha 7 _ _ _ _ hTU hTV
 have hall := binaryGraph p args J.ctag J.atag I.hc I.ha 7 _ _ _ _ hUV hinner
 have hfirst := mpUnderGraph p args base step child J I _ _ _ _ _ _ _ _ _ _ hP hUV hinner
  (liftGraph p args base step child J I _ _ _ _ _ _ hall hP hseed) hk
 exact mpUnderGraph p args base step child J I _ _ _ _ _ _ _ _ _ _ hP hTU hTV hfirst hh
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.GraphRules
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.GraphRules
