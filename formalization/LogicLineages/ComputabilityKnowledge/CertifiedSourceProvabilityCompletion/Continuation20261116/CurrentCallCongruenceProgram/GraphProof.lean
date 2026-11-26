module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.CallGraph
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.InputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.GraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives

theorem leftInputsGraph {arity ctx n : Nat} (p : Program arity) (xs ys codes : List.Vector (Term ctx) n) (i : Fin n) :
 Computes p ((leftInputs n).get i) (pack xs ys codes) (xs.get i) := by
 have h := LiteralRawMP.ConstructorSupportProof.projection p (pack xs ys codes) (i.castAdd (n+n))
 simpa only [leftInputs,List.Vector.get_ofFn,InputProof.left] using h

theorem rightInputsGraph {arity ctx n : Nat} (p : Program arity) (xs ys codes : List.Vector (Term ctx) n) (i : Fin n) :
 Computes p ((rightInputs n).get i) (pack xs ys codes) (ys.get i) := by
 have h := LiteralRawMP.ConstructorSupportProof.projection p (pack xs ys codes) (Fin.natAdd n (i.castAdd n))
 simpa only [rightInputs,List.Vector.get_ofFn,InputProof.right] using h

theorem codeInputsGraph {arity ctx n : Nat} (p : Program arity) (xs ys codes : List.Vector (Term ctx) n) (i : Fin n) :
 Computes p ((codeInputs n).get i) (pack xs ys codes) (codes.get i) := by
 have h := LiteralRawMP.ConstructorSupportProof.projection p (pack xs ys codes) (Fin.natAdd n (Fin.natAdd n i))
 simpa only [codeInputs,List.Vector.get_ofFn,InputProof.code] using h

theorem exactTuple : Targets.InternalTuple := by
 intro arity p n J producerTag I hp ctx xs ys codes
 exact TupleGraph.certificate p (pack xs ys codes) J I (leftInputs n) (rightInputs n) (codeInputs n) xs ys codes
  (leftInputsGraph p xs ys codes) (rightInputsGraph p xs ys codes) (codeInputsGraph p xs ys codes) producerTag hp

theorem exactCall : Targets.InternalCall := by
 intro arity p n J producerTag I hp ctx tag xs ys codes
 apply CallGraph.constructor p (tag ::ᵥ pack xs ys codes) J I (.projection 0) tag
  ((leftInputs n).map tailProgram) ((rightInputs n).map tailProgram) ((codeInputs n).map tailProgram)
  xs ys codes ?_ ?_ ?_ ?_ producerTag hp
 · exact LiteralRawMP.ConstructorSupportProof.projection p (tag ::ᵥ pack xs ys codes) 0
 · intro i
   simpa only [List.Vector.get_map] using InputProof.tail p ((leftInputs n).get i) tag (pack xs ys codes) (xs.get i) (leftInputsGraph p xs ys codes i)
 · intro i
   simpa only [List.Vector.get_map] using InputProof.tail p ((rightInputs n).get i) tag (pack xs ys codes) (ys.get i) (rightInputsGraph p xs ys codes i)
 · intro i
   simpa only [List.Vector.get_map] using InputProof.tail p ((codeInputs n).get i) tag (pack xs ys codes) (codes.get i) (codeInputsGraph p xs ys codes i)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.GraphProof
