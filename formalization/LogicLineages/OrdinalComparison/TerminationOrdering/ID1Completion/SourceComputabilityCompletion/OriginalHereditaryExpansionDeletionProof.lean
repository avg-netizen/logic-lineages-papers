module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionDeletionProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open OriginalHereditaryExpansion OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof

theorem projectionEvaluation {n : Nat} (i : Fin n) (v : List.Vector Nat n) :
    evaluate (.projection i) v = v.get i := rfl

theorem jobEvaluation (packed parameter : Nat) :
    evaluate unpackJob (ofFn ![packed,parameter]) = Nat.pair (Nat.unpair packed).2 parameter := by
  rw [unpackJob,pairOfEvaluation,rightOfEvaluation]
  rfl

theorem rawArgument (P : Program 3) (d k raw : Nat) :
    evaluate (.composition P
      ![.projection 0,.projection 1,InternalApplicationCertificateConstructors.rightOf (.projection 2)])
      (ofFn ![d,k,Nat.pair 0 raw]) = evaluate P (ofFn ![d,k,raw]) := by
  rw [ternaryCompositionEvaluation,rightOfEvaluation]
  congr 1
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  · change d = d
    rfl
  · change k = k
    rfl
  · change (Nat.unpair (Nat.pair 0 raw)).2 = raw
    rw [Nat.unpair_pair]

theorem deletionAt {n : Nat} (c : Nat) (q : Code (Fin n))
    (binders tail : List Ty) (sigma : Ty) :
    evaluate (OriginalHereditaryDeletionRows.observation unpackJob)
      (ofFn ![binders.length,Nat.pair 0 (codeNumber q),
        Nat.pair c (Encodable.encode (binders ++ sigma :: tail))]) =
      jobNumber c ⟨binders ++ tail,eraseCode sigma binders.length q⟩ := by
  rw [OriginalHereditaryDeletionRowsNativeProof.observationPrefix,jobEvaluation]
  unfold OriginalClassContextPrefixNative.erasedPacked
  rw [erasePackedRaw,pairOfEvaluation]
  simp only [Nat.unpair_pair]
  have hraw : evaluate (.composition eraseRaw
      ![.projection 0,.projection 1,InternalApplicationCertificateConstructors.rightOf (.projection 2)])
      (ofFn ![typeNumber sigma,binders.length,Nat.pair 0 (codeNumber q)]) =
      codeNumber (eraseCode sigma binders.length q) := by
    rw [rawArgument]
    exact OriginalRawSyntaxTransportCodeProof.actualRawSyntaxCodeCalibration.2.1 n binders.length sigma q
  rw [hraw]
  rfl

theorem rangeFront (n : Nat) : List.range (n+1) = 0 :: (List.range n).map Nat.succ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [List.range_succ,List.map_append,List.map_singleton,List.cons_append]
      using congrArg (fun xs : List Nat => xs ++ [n+1]) ih

/-- Pure list indexing lemma: the runtime observer is opaque during arithmetic
normalization, so no large Program AST is unfolded by definitional equality. -/
theorem prefixMap (cell : Nat → List Ty → Nat)
    (out : List Ty → List Ty → List Nat)
    (hz : ∀ bs, out bs [] = [])
    (hs : ∀ bs sigma tail, out bs (sigma :: tail) =
      cell bs.length (bs ++ sigma :: tail) :: out (bs ++ [sigma]) tail)
    (bs tail : List Ty) :
    (List.range tail.length).map (fun k => cell (bs.length+k) (bs ++ tail)) = out bs tail := by
  induction tail generalizing bs with
  | nil => simp only [List.length_nil,List.range_zero,List.map_nil,hz]
  | cons sigma tail ih =>
    rw [List.length_cons,rangeFront,List.map_cons,List.map_map,hs]
    simp only [Nat.add_zero]
    congr 1
    have h := ih (bs ++ [sigma])
    rw [← h]
    apply List.map_congr_left
    intro k hk
    simp only [Function.comp_apply,List.length_append,List.length_singleton,
      List.append_assoc,List.singleton_append]
    congr 1
    omega

theorem deletionMap {n : Nat} (c : Nat) (q : Code (Fin n))
    (binders tail : List Ty) :
    (List.range tail.length).map (fun k =>
      evaluate (OriginalHereditaryDeletionRows.observation unpackJob)
        (ofFn ![binders.length+k,Nat.pair 0 (codeNumber q),
          Nat.pair c (Encodable.encode (binders ++ tail))])) =
    (OriginalHereditaryWorkBound.deletionsFrom q binders tail).map (jobNumber c) := by
  apply prefixMap
    (fun k Gamma => evaluate (OriginalHereditaryDeletionRows.observation unpackJob)
      (ofFn ![k,Nat.pair 0 (codeNumber q),Nat.pair c (Encodable.encode Gamma)]))
    (fun bs ts => (OriginalHereditaryWorkBound.deletionsFrom q bs ts).map (jobNumber c))
  · intro bs; rfl
  · intro bs sigma ts
    rw [deletionAt]
    rfl

theorem deletionValuesExact {n : Nat} (c : Nat) (Gamma : List Ty) (q : Code (Fin n)) :
    deletionValues (codeNumber q) (Nat.pair c (Encodable.encode Gamma)) =
      (OriginalHereditaryWorkBound.deletionsFrom q [] Gamma).map (jobNumber c) := by
  unfold deletionValues
  simp only [Nat.unpair_pair,OriginalContextInsertionCalibrationProof.lengthContext]
  unfold OriginalHereditaryDeletionRows.values
  have h := deletionMap c q [] Gamma
  simpa only [List.length_nil,Nat.zero_add,List.nil_append] using h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionDeletionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionDeletionProof
