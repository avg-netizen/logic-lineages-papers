module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowRegistryTermCode
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructorsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowRegistryTermCodeProof
open GorbowSyntax GorbowRegistryTuple GorbowAtomicParameters GorbowRegistryTermCode
open GorbowCodeConstructors

theorem pairCalibration : Comparators.GorbowRegistryTermCode.PairCalibration := by
  intro n a b; rfl

theorem tupleCalibration : Comparators.GorbowRegistryTermCode.TupleCalibration := by
  intro n args
  induction args with
  | nil => rfl
  | cons a args ih =>
    change 2 :: pairRaw (GorbowTermPrefixCode.encode a) (tupleRaw (args.map GorbowTermPrefixCode.encode)) =
      2 :: GorbowTermPrefixCode.encode (pairTerm a (tupleTerm args))
    rw [ih]
    rfl

theorem headerCalibration : Comparators.GorbowRegistryTermCode.HeaderCalibration := by
  intro n arity tag args
  unfold headerRaw headerTerm
  rw [← GorbowCodeConstructorsProof.numeralCalibration n arity,
    ← GorbowCodeConstructorsProof.numeralCalibration n tag,tupleCalibration]
  rfl

theorem evaluationCalibration : Comparators.GorbowRegistryTermCode.EvaluationCalibration := by
  intro n t
  exact congrArg (List.cons 5) (headerCalibration n 1 1 [t])

theorem guardCalibration : Comparators.GorbowRegistryTermCode.GuardCalibration := by
  intro n t
  exact congrArg (List.cons 1) (headerCalibration n 1 2 [t])

private theorem prefixCommutes (n : Nat) :
    closurePrefix ++ (List.replicate n closurePrefix).flatten =
      (List.replicate n closurePrefix).flatten ++ closurePrefix := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ,List.flatten_cons,List.append_assoc]; rw [ih]
private theorem closeSucc (n : Nat) (raw : List Nat) :
    closeRaw (n+1) raw=closeRaw n (closurePrefix++raw) := by
  simp only [closeRaw,List.replicate_succ,List.flatten_cons]
  rw [← List.append_assoc,prefixCommutes,List.append_assoc]

theorem closureCalibration : Comparators.GorbowRegistryTermCode.ClosureCalibration := by
  intro n
  induction n with
  | zero => intro φ; rfl
  | succ n ih =>
    intro φ
    rw [closeSucc]
    have hc : closurePrefix ++ GorbowFormulaPrefixCode.encode φ =
        GorbowFormulaPrefixCode.encode (.all (.imp
          (GorbowSortedQuantifierTruth.arithmeticTermGuard (.var 0)) φ)) := by
      rw [show closurePrefix=[10,7] ++ GorbowFormulaPrefixCode.encode
        (GorbowSortedQuantifierTruth.arithmeticTermGuard (.var 0 : Term (n+1))) from
        congrArg (List.append [10,7]) (guardCalibration (n+1) (.var 0))]
      rfl
    rw [hc]
    exact ih _

private theorem pr_binary (tag : Nat) : Primrec (fun p : List Nat × List Nat => binary tag p.1 p.2) :=
  Primrec.list_cons.comp (Primrec.const tag) (Primrec.list_append.comp Primrec.fst Primrec.snd)
private theorem pr_pair : Primrec (fun p : List Nat × List Nat => pairRaw p.1 p.2) := by
  have ha := pr_binary 3
  have hm := (pr_binary 4).comp (ha.pair ha)
  exact (pr_binary 3).comp (hm.pair Primrec.fst)
private theorem pr_tuple : Primrec tupleRaw :=
  Primrec.list_foldr Primrec.id (Primrec.const [1])
    (Primrec.list_cons.comp (Primrec.const 2) (pr_pair.comp Primrec.snd)).to₂
private theorem pr_header : Primrec (fun p : Nat × Nat × List (List Nat) => headerRaw p.1 p.2.1 p.2.2) := by
  have hn := GorbowCodeConstructorsProof.uniformPrograms.2.2.2.1
  exact pr_pair.comp ((hn.comp Primrec.fst).pair (pr_pair.comp
    ((hn.comp (Primrec.fst.comp Primrec.snd)).pair (pr_tuple.comp (Primrec.snd.comp Primrec.snd)))))
private theorem pr_singleHeader (arity tag : Nat) : Primrec (fun raw : List Nat => headerRaw arity tag [raw]) :=
  pr_header.comp ((Primrec.const arity).pair ((Primrec.const tag).pair
    (Primrec.list_cons.comp Primrec.id (Primrec.const []))))
private theorem pr_evaluation : Primrec evaluationRaw :=
  Primrec.list_cons.comp (Primrec.const 5) (pr_singleHeader 1 1)
private theorem pr_guard : Primrec arithmeticGuardRaw :=
  Primrec.list_cons.comp (Primrec.const 1) (pr_singleHeader 1 2)
private theorem pr_close : Primrec (fun p : Nat × List Nat => closeRaw p.1 p.2) := by
  have hr : Primrec (fun n : Nat => List.replicate n closurePrefix) :=
    (Primrec.list_map Primrec.list_range (Primrec.const closurePrefix).to₂).of_eq (by intro n; simp)
  exact Primrec.list_append.comp (Primrec.list_flatten.comp (hr.comp Primrec.fst)) Primrec.snd

theorem uniformPrograms : Comparators.GorbowRegistryTermCode.UniformPrograms :=
  ⟨pr_pair,pr_tuple,pr_header,pr_evaluation,pr_guard,pr_close⟩
theorem gorbowRegistryTermCode : Comparators.GorbowRegistryTermCode.Target :=
  ⟨pairCalibration,tupleCalibration,headerCalibration,evaluationCalibration,guardCalibration,closureCalibration,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowRegistryTermCodeProof
