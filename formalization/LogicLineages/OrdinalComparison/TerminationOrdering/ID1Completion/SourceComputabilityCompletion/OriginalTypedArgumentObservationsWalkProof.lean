module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsWalkProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalTypedArgumentObservations OriginalTypedArgumentObservationsEvaluationProof
open InternalApplicationCertificateConstructorsEvaluationProof OriginalRawSyntaxTransportEvaluationSupportProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedMultisetNumeric

 def observations {n : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
 (R : Program 2) (args : AuxArguments (Fin n) arity Gamma types) (parameter : Nat) : List Nat :=
 (argumentList args).map (fun q => Nat.pair (typeNumber q.1)
   (evaluate R (ofFn ![packedNumber q,parameter])))

theorem walkSuccessor (R : Program 2) (count initial parameter : Nat) :
 evaluate (walk R) (ofFn ![count+1,initial,parameter]) =
 evaluate (walkStep R) (ofFn ![evaluate (walk R) (ofFn ![count,initial,parameter]),parameter]) := by
 change evaluate (walkStep R) (ofFn fun i : Fin 2 =>
   evaluate (![Program.projection (1 : Fin 4),Program.projection (3 : Fin 4)] i)
     (ofFn ![count,evaluate (walk R) (ofFn ![count,initial,parameter]),initial,parameter])) = _
 congr 1

theorem walkFirst (R : Program 2) (count initial parameter : Nat) :
 evaluate (walk R) (ofFn ![count+1,initial,parameter]) =
 evaluate (walk R) (ofFn ![count,evaluate (walkStep R) (ofFn ![initial,parameter]),parameter]) := by
 induction count with
 | zero => rw [walkSuccessor]; rfl
 | succ count ih => rw [walkSuccessor,ih,walkSuccessor]

theorem walkNil (R : Program 2) (count acc parameter : Nat) :
 evaluate (walk R) (ofFn ![count,Nat.pair (Nat.pair 6 0) acc,parameter]) =
 Nat.pair (Nat.pair 6 0) acc := by
 induction count with
 | zero => rfl
 | succ count ih => rw [walkSuccessor,ih]; exact stepNil R acc parameter

/-- Full native walk invariant. The accumulated list is reversed, and the
same external parameter is passed to every original typed child. -/
theorem walkArguments {n : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
 (R : Program 2) (args : AuxArguments (Fin n) arity Gamma types) (parameter : Nat) :
 ∀ (fuel : Nat) (acc : List Nat), codeNumber (argumentsCode args) < fuel →
 evaluate (walk R) (ofFn ![fuel,Nat.pair (codeNumber (argumentsCode args)) (numbersNumber acc),parameter]) =
 Nat.pair (Nat.pair 6 0) (numbersNumber ((observations R args parameter).reverse ++ acc)) := by
 induction types with
 | nil =>
   cases args
   intro fuel acc _
   simpa only [argumentsCode,codeNumber,observations,argumentList,List.map_nil,List.reverse_nil,List.nil_append] using
     walkNil R fuel (numbersNumber acc) parameter
 | cons typ types ih =>
   cases args with
   | cons q rest =>
     intro fuel acc hf
     cases fuel with
     | zero => omega
     | succ fuel =>
       have ht := rawTailBound (typeNumber typ) (codeNumber (termCode q)) (codeNumber (argumentsCode rest))
       have hrest : codeNumber (argumentsCode rest) < fuel := by
         simp only [argumentsCode,codeNumber] at hf
         omega
       rw [walkFirst]
       have hs := stepCons R (typeNumber typ) (codeNumber (termCode q))
         (codeNumber (argumentsCode rest)) (numbersNumber acc) parameter
       change evaluate (walkStep R) (ofFn ![Nat.pair (codeNumber (argumentsCode (.cons q rest))) (numbersNumber acc),parameter]) = _ at hs
       rw [hs]
       let value := Nat.pair (typeNumber typ) (evaluate R (ofFn ![packedNumber ⟨typ,q⟩,parameter]))
       have hi := ih rest fuel (value :: acc) hrest
       simpa only [observations,argumentList,List.map_cons,List.reverse_cons,List.append_assoc,
         List.singleton_append,packedNumber,numbersNumber,value,InternalEqualityTestEvaluationProof.vectorTwo,
         Matrix.cons_val_zero,Matrix.cons_val_one] using hi

theorem reversedEvaluation {n : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
 (R : Program 2) (args : AuxArguments (Fin n) arity Gamma types) (parameter : Nat) :
 evaluate (reversedObservations R) (ofFn ![codeNumber (argumentsCode args),parameter]) =
 numbersNumber (observations R args parameter).reverse := by
 rw [reversedObservations,rightOfEvaluation,walked,ternaryCompositionEvaluation]
 simp only [OriginalRawSyntaxTransportEvaluationSupportProof.succOfEvaluation,initial,pairOfEvaluation,constantEvaluation,evaluate]
 have hw := walkArguments R args parameter (codeNumber (argumentsCode args)+1) [] (by omega)
 change (Nat.unpair (evaluate (walk R) (ofFn ![codeNumber (argumentsCode args)+1,
   Nat.pair (codeNumber (argumentsCode args)) 0,parameter]))).2 = _
 simp only [numbersNumber,List.append_nil] at hw
 rw [hw,Nat.unpair_pair]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsWalkProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsWalkProof
