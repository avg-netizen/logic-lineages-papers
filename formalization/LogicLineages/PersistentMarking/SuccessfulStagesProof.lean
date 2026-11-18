import LogicLineages.PersistentMarking.SuccessfulPluggingProof
import LogicLineages.PersistentMarking.PrefixStageSupport
namespace LogicLineages.PersistentMarking.SuccessfulStagesProof
open Spine PrefixStageSupport

theorem functionalStep (g : Head) (σ : Ty) (base extras : Args) (a : Expr) (rest : Args) (τ : Ty)
    (hc : consumeTypes σ (.cons a rest) = some τ) :
    ∃ ρ, consumeTypes σ (.cons a .nil) = some ρ ∧
      apply (.marked g ρ base (extras.append (.cons a .nil))) rest =
        some (.marked g τ base (extras.append (.cons a rest))) := by
  cases σ with
  | ground => simp [consumeTypes] at hc
  | arrow α β =>
    by_cases ht : a.type = α
    · have htail : consumeTypes β rest = some τ := by simpa only [consumeTypes,ht,if_true] using hc
      refine ⟨β,by simp only [consumeTypes,ht,if_true],?_⟩
      cases rest with
      | nil =>
        simp only [consumeTypes,Option.some.injEq] at htail
        subst τ
        simp only [apply]
      | cons b bs =>
        simp only [apply,applyAux,htail,Option.map_some,SubstitutionProof.emptyArgsSubstitution,appendAssoc,Args.append]
    · simp [consumeTypes,ht] at hc

theorem firstStep (q : Expr) (a : Expr) (rest values : Args) (r : Expr)
    (hc : applyAux q (.cons a rest) values = some r) :
    ∃ m, applyAux q (.cons a .nil) values = some m ∧ apply m rest = some r := by
  cases q with
  | free σ x => simp [applyAux] at hc
  | bound σ i => simp [applyAux] at hc
  | lam σ body =>
    by_cases ht : a.type = σ
    · have hi : applyAux body rest (Args.nil.append (.cons a values)) = some r := by
        simpa only [applyAux,ht,if_true,Args.append] using hc
      have hh := SuccessfulPluggingProof.plugging body .nil (.cons a values) rest r hi
      refine ⟨substitute (.cons a values) 0 body,?_,?_⟩
      · simp only [applyAux,ht,if_true]
      · exact SuccessfulPluggingProof.auxNilValues hh
    · simp [applyAux,ht] at hc
  | head f base =>
    cases htypes : consumeTypes f.result (.cons a rest) with
    | none => simp [applyAux,htypes] at hc
    | some τ =>
      simp only [applyAux,htypes,Option.map_some,Option.some.injEq] at hc
      subst r
      obtain ⟨ρ,hone,hrest⟩ := functionalStep f f.result (substituteArgs values 0 base) .nil a rest τ htypes
      refine ⟨.marked f ρ (substituteArgs values 0 base) (.cons a .nil),?_,?_⟩
      · simp only [applyAux,hone,Option.map_some]
      · simpa only [Args.append] using hrest
  | marked f σ base extras =>
    cases htypes : consumeTypes σ (.cons a rest) with
    | none => simp [applyAux,htypes] at hc
    | some τ =>
      simp only [applyAux,htypes,Option.map_some,Option.some.injEq] at hc
      subst r
      obtain ⟨ρ,hone,hrest⟩ := functionalStep f σ (substituteArgs values 0 base) (substituteArgs values 0 extras) a rest τ htypes
      refine ⟨.marked f ρ (substituteArgs values 0 base) ((substituteArgs values 0 extras).append (.cons a .nil)),?_,hrest⟩
      simp only [applyAux,hone,Option.map_some]

theorem stages (q : Expr) (args : Args) (r : Expr) (h : apply q args = some r) : unaryCalls q args = some r := by
  cases args with
  | nil => simpa only [apply,unaryCalls] using h
  | cons a rest =>
    obtain ⟨m,hm,hrest⟩ := firstStep q a rest .nil r h
    have hi := stages m rest r hrest
    simpa only [unaryCalls,apply,hm,Option.bind_some] using hi
termination_by sizeOf args

theorem successfulUnaryStages : ApplicationCovarianceTargets.SuccessfulUnaryStages := stages
end LogicLineages.PersistentMarking.SuccessfulStagesProof
