module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.RawProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open NumberedLeastCodeRepresentative Source
open InternalRawListRecursionEvaluationProof

theorem caseStepValue (head rest : Nat) : evaluate caseStep (head ::ᵥ rest ::ᵥ nil) =
    1 + Nat.pair (Nat.pair 2 head) (1 + Nat.pair (Nat.pair 3 head) rest) := by
  simp only [caseStep,consOfEvaluation,pairOfEvaluation,constantEvaluation]
  rfl

theorem casesValue (xs : List Nat) : evaluate casesRecursors (ofFn ![numbersNumber xs]) =
    numbersNumber (xs.flatMap (fun x => [Nat.pair 2 x,Nat.pair 3 x])) := by
  have h := actualRawListRecursionEvaluation 0 (constant 0 0) caseStep nil (numbersNumber xs)
  change evaluate casesRecursors (ofFn ![numbersNumber xs]) = _ at h
  rw [h,numbersRoundTrip]
  change xs.foldr (fun head rest => evaluate caseStep (head ::ᵥ rest ::ᵥ nil)) 0 = _
  clear h
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.foldr_cons,caseStepValue,ih]
    simp only [List.flatMap_cons,List.cons_append,List.nil_append,numbersNumber]

theorem appStepValue (head rest sigma : Nat) : evaluate appStep (head ::ᵥ rest ::ᵥ sigma ::ᵥ nil) =
    1 + Nat.pair (Nat.pair 4 (Nat.pair sigma head)) rest := by
  simp only [appStep,consOfEvaluation,pairOfEvaluation,constantEvaluation]
  rfl

theorem appRowValue (xs : List Nat) (sigma : Nat) : evaluate appRow (ofFn ![numbersNumber xs,sigma]) =
    numbersNumber (xs.map (fun tau => Nat.pair 4 (Nat.pair sigma tau))) := by
  have h := actualRawListRecursionEvaluation 1 (constant 1 0) appStep (sigma ::ᵥ nil) (numbersNumber xs)
  change evaluate appRow (ofFn ![numbersNumber xs,sigma]) = _ at h
  rw [h,numbersRoundTrip]
  change xs.foldr (fun head rest => evaluate appStep (head ::ᵥ rest ::ᵥ sigma ::ᵥ nil)) 0 = _
  clear h
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.foldr_cons,appStepValue,ih,List.map_cons,numbersNumber]

theorem appsStepValue (sigma : Nat) (rest types : List Nat) :
    evaluate appsStep (sigma ::ᵥ numbersNumber rest ::ᵥ numbersNumber types ::ᵥ nil) =
      numbersNumber (types.map (fun tau => Nat.pair 4 (Nat.pair sigma tau)) ++ rest) := by
  rw [appsStep,binaryCompositionEvaluation]
  have hr : evaluate (.composition appRow ![.projection 2,.projection 0])
      (sigma ::ᵥ numbersNumber rest ::ᵥ numbersNumber types ::ᵥ nil) =
      numbersNumber (types.map (fun tau => Nat.pair 4 (Nat.pair sigma tau))) := appRowValue types sigma
  rw [hr]
  have hp : evaluate (.projection (1 : Fin 3)) (sigma ::ᵥ numbersNumber rest ::ᵥ numbersNumber types ::ᵥ nil) = numbersNumber rest := rfl
  rw [hp]
  have ha := PrimaryExpansion.NativeProof.appendEvaluation
    (numbersNumber (types.map (fun tau => Nat.pair 4 (Nat.pair sigma tau)))) rest
  simpa only [numbersRoundTrip,Option.getD_some] using ha

theorem appsFold (front types : List Nat) :
    front.foldr (fun head rest => evaluate appsStep (head ::ᵥ rest ::ᵥ numbersNumber types ::ᵥ nil)) 0 =
      numbersNumber (front.flatMap (fun sigma => types.map (fun tau => Nat.pair 4 (Nat.pair sigma tau)))) := by
  induction front with
  | nil => rfl
  | cons head front ih => rw [List.foldr_cons,ih,appsStepValue,List.flatMap_cons]

theorem applicationsValue (types : List Nat) : evaluate applications (ofFn ![numbersNumber types]) =
    numbersNumber (types.flatMap (fun sigma => types.map (fun tau => Nat.pair 4 (Nat.pair sigma tau)))) := by
  have h := actualRawListRecursionEvaluation 1 (constant 1 0) appsStep (numbersNumber types ::ᵥ nil) (numbersNumber types)
  change evaluate applications (ofFn ![numbersNumber types]) = _ at h
  rw [h,numbersRoundTrip]
  exact appsFold types types

theorem rankedStepValue (head rest : Nat) : evaluate rankedStep (head ::ᵥ rest ::ᵥ nil) =
    1 + Nat.pair (Nat.pair 5 head) rest := by
  simp only [rankedStep,consOfEvaluation,pairOfEvaluation,constantEvaluation]
  rfl

theorem rankedValue (xs : List Nat) : evaluate rankedHeads (ofFn ![numbersNumber xs]) =
    numbersNumber (xs.map (fun x => Nat.pair 5 x)) := by
  have h := actualRawListRecursionEvaluation 0 (constant 0 0) rankedStep nil (numbersNumber xs)
  change evaluate rankedHeads (ofFn ![numbersNumber xs]) = _ at h
  rw [h,numbersRoundTrip]
  change xs.foldr (fun head rest => evaluate rankedStep (head ::ᵥ rest ::ᵥ nil)) 0 = _
  clear h
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.foldr_cons,rankedStepValue,ih,List.map_cons,numbersNumber]

theorem appendValue (xs ys : List Nat) : evaluate InternalApplicationValidityStackAppend.append
    (ofFn ![numbersNumber xs,numbersNumber ys]) = numbersNumber (xs ++ ys) := by
  simpa only [numbersRoundTrip,Option.getD_some] using PrimaryExpansion.NativeProof.appendEvaluation (numbersNumber xs) ys

theorem rawValue (symbols types : List Nat) : evaluate rawWindow (ofFn ![numbersNumber symbols,numbersNumber types]) =
    numbersNumber ([Nat.pair 0 0,Nat.pair 1 0] ++
      types.flatMap (fun tau => [Nat.pair 2 tau,Nat.pair 3 tau]) ++
      types.flatMap (fun sigma => types.map (fun tau => Nat.pair 4 (Nat.pair sigma tau))) ++
      symbols.map (fun s => Nat.pair 5 s)) := by
  simp only [rawWindow,consOfEvaluation,pairOfEvaluation,constantEvaluation,
    binaryCompositionEvaluation,unaryCompositionEvaluation]
  change 1 + Nat.pair (Nat.pair 0 0) (1 + Nat.pair (Nat.pair 1 0)
    (evaluate InternalApplicationValidityStackAppend.append (ofFn ![
      evaluate casesRecursors (ofFn ![numbersNumber types]),
      evaluate InternalApplicationValidityStackAppend.append (ofFn ![
        evaluate applications (ofFn ![numbersNumber types]),evaluate rankedHeads (ofFn ![numbersNumber symbols])])]))) = _
  rw [casesValue,applicationsValue,rankedValue,appendValue,appendValue]
  simp only [List.cons_append,List.nil_append,numbersNumber,List.append_assoc]

theorem nativeRawWindow : Targets.NativeRawWindow := by
  intro n symbols types
  rw [rawValue]
  congr 1
  simp [NumberedFiniteUniverse.rawHeadWindow,List.map_append,List.map_flatMap,List.flatMap_map,List.map_map,
    Function.comp_def,NumberedAuxiliaryCoding.headCode,headNumber]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.RawProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.RawProof
