module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.UnaryGraph
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.BinaryGraph
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives

theorem operation {arity inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : Installation p J) (multiply : Bool) (a b : Program inputs) (av bv : Term ctx)
 (ha : Computes p a args av) (hb : Computes p b args bv) :
 Computes p (FixedFormulaSubstitution.binary (if multiply then 4 else 3) a b) args (binaryValue J multiply av bv) :=
 GraphSupport.binaryCode p args J I _ _ _ _ _ ha hb

theorem binaryGraph {arity inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : Installation p J) (multiply : Bool) (a b c d hac hbd : Program inputs)
 (av bv cv dv hv kv : Term ctx)
 (ha : Computes p a args av) (hb : Computes p b args bv) (hc : Computes p c args cv) (hd : Computes p d args dv)
 (hh : Computes p hac args hv) (hk : Computes p hbd args kv) :
 Computes p (CurrentCallCongruenceProgram.binary multiply a b c d hac hbd) args
  (binaryCertificate J multiply av bv cv dv hv kv) := by
 have hp := UnaryGraph.ordinary p args J I binaryEnvironment (binaryTerm multiply (.var 0) (.var 1))
  (b ::ᵥ nil) (bv ::ᵥ nil) a c hac av cv hv (fun i => Fin.cases hb (fun j => Fin.elim0 j) i) ha hc hh
 have hq := UnaryGraph.ordinary p args J I binaryEnvironment (binaryTerm multiply (.var 1) (.var 0))
  (c ::ᵥ nil) (cv ::ᵥ nil) b d hbd bv dv kv (fun i => Fin.cases hc (fun j => Fin.elim0 j) i) hb hd hk
 exact TransitivityGraph.transitivityGraph p args J I _ _ _ _ _ _ _ _ _ _
  (operation p args J I multiply a b av bv ha hb)
  (operation p args J I multiply c b cv bv hc hb)
  (operation p args J I multiply c d cv dv hc hd) hp hq

theorem pairValueGraph {arity inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : Installation p J) (a b : Program inputs) (av bv : Term ctx)
 (ha : Computes p a args av) (hb : Computes p b args bv) :
 Computes p (pairCode a b) args (pairValue J av bv) := by
 have hs := operation p args J I false a b av bv ha hb
 exact operation p args J I false _ a _ av (operation p args J I true _ _ _ _ hs hs) ha

theorem pairGraph {arity inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : Installation p J) (a b c d hac hbd : Program inputs)
 (av bv cv dv hv kv : Term ctx)
 (ha : Computes p a args av) (hb : Computes p b args bv) (hc : Computes p c args cv) (hd : Computes p d args dv)
 (hh : Computes p hac args hv) (hk : Computes p hbd args kv) :
 Computes p (pair a b c d hac hbd) args (pairCertificate J av bv cv dv hv kv) := by
 have hs := binaryGraph p args J I false a b c d hac hbd av bv cv dv hv kv ha hb hc hd hh hk
 have hab := operation p args J I false a b av bv ha hb
 have hcd := operation p args J I false c d cv dv hc hd
 have hm := binaryGraph p args J I true _ _ _ _ _ _ _ _ _ _ _ _ hab hab hcd hcd hs hs
 exact binaryGraph p args J I false _ a _ c _ hac _ av _ cv _ hv
  (operation p args J I true _ _ _ _ hab hab) ha (operation p args J I true _ _ _ _ hcd hcd) hc hm hh

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.BinaryGraph
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.BinaryGraph
