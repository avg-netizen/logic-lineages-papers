module
public import LogicLineages.OrdinalComparison.ComparisonQueryTargets
public import LogicLineages.OrdinalComparison.ComparisonExpansionProgramProof
public import LogicLineages.OrdinalComparison.ProfileCompositionProof
public import LogicLineages.OrdinalComparison.LimitPairCertificateProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonQuery

theorem context_primitive : Primrec encodedComparisonHeadContext := by
  have h := LimitPairCertificate.principal_source.1.comp (Primrec.fst.comp ComparisonExpansion.outer_primitive)
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
    (Primrec₂.natPair.comp h (Primrec.const 1))) (Primrec.const 3)

theorem contexts_primitive : Primrec encodedComparisonQueryContexts :=
  Primrec.list_cons.comp (Primrec.const 1)
    (Primrec.list_cons.comp (Primrec.const (positiveExprEncode (.head profileOmegaNote .input)))
      (Primrec.list_cons.comp (context_primitive.comp Primrec.fst)
        (Primrec.list_cons.comp (context_primitive.comp Primrec.snd) (Primrec.const []))))

theorem profiles_primitive : Primrec encodedComparisonQueryProfiles := by
  have hl : Primrec (fun q : ComparisonQuery => q.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun q : ComparisonQuery => q.2.2) := Primrec.snd.comp Primrec.snd
  have hbase := Primrec.list_cons.comp hl (Primrec.list_cons.comp hr (Primrec.const []))
  have hctx : Primrec (fun q : ComparisonQuery => encodedComparisonQueryContexts q.1) := contexts_primitive.comp Primrec.fst
  have hmap : Primrec₂ (fun q : ComparisonQuery => fun p : Nat =>
      (encodedComparisonQueryContexts q.1).map (encodedProfileCompose p)) :=
    Primrec.list_map (contexts_primitive.comp (Primrec.fst.comp Primrec.fst))
      (ProfileComposition.program.1.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have hinit : Primrec (fun q : ComparisonQuery => [1,q.2.1,q.2.2]) :=
    Primrec.list_cons.comp (Primrec.const 1) hbase
  have hcomp : Primrec (fun q : ComparisonQuery => [q.2.1,q.2.2].flatMap
      (fun p => (encodedComparisonQueryContexts q.1).map (encodedProfileCompose p))) :=
    Primrec.list_flatMap hbase hmap
  have hall : Primrec (fun q : ComparisonQuery =>
      ([1,q.2.1,q.2.2]++encodedComparisonQueryContexts q.1)++[q.2.1,q.2.2].flatMap
        (fun p => (encodedComparisonQueryContexts q.1).map (encodedProfileCompose p))) :=
    Primrec.list_append.comp (Primrec.list_append.comp hinit hctx) hcomp
  exact hall

theorem requests_primitive : Primrec encodedComparisonQueryRequests := by
  have hlocal : Primrec₂ (fun _ : ComparisonQuery => fun p : Nat => [(p,1),(1,p)]) :=
    Primrec.list_cons.comp (Primrec.snd.pair (Primrec.const 1))
      (Primrec.list_cons.comp ((Primrec.const 1).pair Primrec.snd) (Primrec.const []))
  exact Primrec.list_append.comp (Primrec.const [(1,1)])
    (Primrec.list_flatMap profiles_primitive hlocal)

theorem children_primitive : Primrec encodedComparisonQueryChildren := by
  have hsource : Primrec (fun q : ComparisonQuery => encodedComparisonChildren q.1.1 q.1.2) :=
    ComparisonExpansion.children_primitive.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  have hmap : Primrec₂ (fun q : ComparisonQuery => fun source : Nat × Nat =>
      (encodedComparisonQueryRequests q).map (fun profiles => (source,profiles))) :=
    Primrec.list_map (requests_primitive.comp Primrec.fst)
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
  exact Primrec.list_flatMap hsource hmap

theorem frontier_step_primitive : Primrec encodedComparisonQueryFrontierStep :=
  Primrec.list_flatMap Primrec.id (children_primitive.comp Primrec.snd)

theorem frontier_primitive : Primrec₂ encodedComparisonQueryFrontier :=
  Primrec.nat_iterate (α := ComparisonQuery × Nat) (β := List ComparisonQuery) Primrec.snd
    (Primrec.list_cons.comp Primrec.fst (Primrec.const [])) (frontier_step_primitive.comp Primrec.snd)

theorem program : Targets.ComparisonQueryProgramsPrimitiveRecursive :=
  ⟨context_primitive,contexts_primitive,profiles_primitive,requests_primitive,
    children_primitive,frontier_step_primitive,frontier_primitive⟩

end LogicLineages.OrdinalComparison.ComparisonQuery
