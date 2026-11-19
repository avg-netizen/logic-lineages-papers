module
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionTreePresentationTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionStatementChecks
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverageStatementChecks
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecisionTreePresentation

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open GroundEquivalence ExistentialPlan
open OriginalInput (Query)
open RawSourceDAG (Code)
open RawSourceDAG.InputCompiler (encodeInput)

private theorem rawContextExact (n : Nat) :
    rawContext n = (List.replicate n Ty.ground).map SyntaxCode.typeCode := by
  simp [rawContext,SyntaxCode.typeCode]

private theorem positiveRepresentation {Γ : List Ty} (hg : ∀ t ∈ Γ, t = Ty.ground)
    (ν : OrdinalComponent Γ → Nat) (h : ∀ c, 0 < ν c) :
    ∃ ρ : Variable Γ .ground → Nat, (fun c => inputs ρ c+1) = ν := by
  refine ⟨fun v => ν ⟨Ty.ground,v,0⟩ - 1,?_⟩
  funext c
  rcases c with ⟨σ,v,i⟩
  have t := AbsoluteObserver.groundType hg v
  cases t
  have hi : i = 0 := Fin.eq_zero i
  subst i
  change ν ⟨Ty.ground,v,0⟩ - 1 + 1 = ν ⟨Ty.ground,v,0⟩
  have hv := h ⟨Ty.ground,v,0⟩
  omega

theorem originalUniversalExact (p : AdmissibleSum.Policy) (f : Nat → Nat) (strict : Bool)
    {Γ : List Ty} {σ τ : Ty} (hg : ∀ t ∈ Γ, t = Ty.ground) (a : Input Γ σ) (b : Input Γ τ) :
    OriginalUniversal p f strict a.term b.term ↔ CurrentDecision.Universal p f strict a b := by
  constructor
  · rintro ⟨av,bv,ha,hb,h⟩
    exact ⟨av,bv,ha,hb,fun ρ => h _ (fun _ => Nat.zero_lt_succ _)⟩
  · rintro ⟨av,bv,ha,hb,h⟩
    refine ⟨av,bv,ha,hb,?_⟩
    intro ν hν
    obtain ⟨ρ,rfl⟩ := positiveRepresentation hg ν hν
    exact h ρ

theorem compileOriginalTrees : CurrentDecisionTreePresentationTargets.CompileOriginalTrees := by
  intro p f hf n strict σ τ a b
  let Γ := List.replicate n Ty.ground
  let q : Query := (n,strict,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)
  let da := CurrentTreeInputCoverage.input a
  let db := CurrentTreeInputCoverage.input b
  let qD : CurrentDecision.QueryCode := (strict,RawSourceDAG.encode ⟨Γ,σ,da⟩,
    RawSourceDAG.encode ⟨Γ,τ,db⟩)
  have ha := CurrentTreeInputCoverage.StatementChecks.actual_tree_codes Γ σ a
  have hb := CurrentTreeInputCoverage.StatementChecks.actual_tree_codes Γ τ b
  have hg : ∀ t ∈ Γ, t = Ty.ground := fun _ ht => List.eq_of_mem_replicate ht
  have hD : toDAGs q = some qD := by
    have ha' : CurrentTreeInputCoverage.compile (rawContext n) (SyntaxCode.encodeTerm a) =
        some (RawSourceDAG.encode ⟨Γ,σ,da⟩) := by
      rw [rawContextExact n]
      exact ha.2.1
    have hb' : CurrentTreeInputCoverage.compile (rawContext n) (SyntaxCode.encodeTerm b) =
        some (RawSourceDAG.encode ⟨Γ,τ,db⟩) := by
      rw [rawContextExact n]
      exact hb.2.1
    change ((CurrentTreeInputCoverage.compile (rawContext n) (SyntaxCode.encodeTerm a)).bind
      fun x => (CurrentTreeInputCoverage.compile (rawContext n) (SyntaxCode.encodeTerm b)).bind
        fun y => some (strict,x,y)) = some qD
    rw [ha',hb'] <;> rfl
  have hU : OriginalUniversal p f strict a b ↔ CurrentDecision.Universal p f strict da db := by
    have h := originalUniversalExact p f strict hg da db
    rw [show da.term = a from ha.1,show db.term = b from hb.1] at h
    exact h
  obtain ⟨r,hr,hU'⟩ := CurrentDecision.StatementChecks.general_reduction p f hf strict n σ τ da db
  have hArith : toArithmetic p f q = some (n+6,encodeInput r) := by
    have hq : CurrentDecision.toArithmetic p f qD = (n+6,encodeInput r) := hr
    simp [toArithmetic,hD,hq]
  obtain ⟨hC,hS,hW⟩ := CurrentDecision.StatementChecks.arithmetic_reduction p f hf (n+6) r
  have hSat := hU.trans hU'
  refine ⟨hD,r,hArith,?_,hSat,?_,?_⟩
  · change (toArithmetic p f q).map CurrentCompiler.compile = some (CurrentCompiler.expected r)
    rw [hArith,Option.map_some,hC]
  · exact hSat.trans hS.symm
  · exact hSat.trans hW.symm

theorem groundInclusion : CurrentDecisionTreePresentationTargets.GroundInclusion := by
  intro p f strict n a b
  let Γ := List.replicate n Ty.ground
  let da := CurrentTreeInputCoverage.input a
  let db := CurrentTreeInputCoverage.input b
  have hg : ∀ t ∈ Γ, t = Ty.ground := fun _ ht => List.eq_of_mem_replicate ht
  have h := (originalUniversalExact p f strict hg da db).trans
    (CurrentDecision.StatementChecks.ground_specialization p f strict n da db)
  unfold CurrentDecision.Ground at h
  rw [show da.term = a from CurrentTreeInputCoverage.inputTerm a,
    show db.term = b from CurrentTreeInputCoverage.inputTerm b] at h
  exact h

theorem rawRejection : CurrentDecisionTreePresentationTargets.RawRejection := by
  intro q
  have ha := CurrentTreeInputCoverage.StatementChecks.actual_raw_program.1 (rawContext q.1) q.2.2.1
  have hb := CurrentTreeInputCoverage.StatementChecks.actual_raw_program.1 (rawContext q.1) q.2.2.2
  have hd : toDAGs q = none ↔ SyntaxCode.check (rawContext q.1) q.2.2.1 = none ∨
      SyntaxCode.check (rawContext q.1) q.2.2.2 = none := by
    rw [← ha,← hb]
    cases hca : CurrentTreeInputCoverage.compile (rawContext q.1) q.2.2.1 <;>
      cases hcb : CurrentTreeInputCoverage.compile (rawContext q.1) q.2.2.2 <;>
      simp [toDAGs,hca,hcb]
  refine ⟨hd,?_⟩
  intro p f
  exact ⟨Option.map_eq_none_iff.trans hd,
    Option.map_eq_none_iff.trans (Option.map_eq_none_iff.trans hd)⟩

theorem effective : CurrentDecisionTreePresentationTargets.Effective := by
  have hc := CurrentTreeInputCoverage.StatementChecks.actual_raw_program.2
  have hz : Primrec rawContext := by
    have h : Primrec (fun n : Nat => (List.range n).map (fun _ => (0 : Nat))) :=
      Primrec.list_map Primrec.list_range (Primrec.const 0).to₂
    exact h.of_eq (fun n => by simp [rawContext])
  have hΓ := hz.to_comp.comp (Computable.fst : Computable (fun q : Query => q.1))
  have ha : Computable (fun q : Query => CurrentTreeInputCoverage.compile (rawContext q.1) q.2.2.1) :=
    hc.comp hΓ (Computable.fst.comp (Computable.snd.comp Computable.snd))
  have hb : Computable (fun q : Query => CurrentTreeInputCoverage.compile (rawContext q.1) q.2.2.2) :=
    hc.comp hΓ (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hm : Computable₂ (fun (x : Query × Code) (b : Code) => (x.1.2.1,x.2,b)) := by
    have hq : Computable (fun x : (Query × Code) × Code => x.1.1) :=
      Computable.fst.comp Computable.fst
    exact ((Computable.fst.comp (Computable.snd.comp hq)).pair
      ((Computable.snd.comp Computable.fst).pair Computable.snd)).to₂
  have htail : Computable₂ (fun (q : Query) (a : Code) =>
      (CurrentTreeInputCoverage.compile (rawContext q.1) q.2.2.2).map (fun b => (q.2.1,a,b))) :=
    (Computable.option_map (hb.comp Computable.fst) hm).to₂
  have hdag : Computable toDAGs := by
    apply (Computable.option_bind ha htail).of_eq
    intro q
    simp only [toDAGs,Option.map_eq_bind,Function.comp_def] <;> rfl
  refine ⟨hdag,?_⟩
  intro p hp f hfc hf
  have h := CurrentDecision.StatementChecks.actual_effective_maps
  have hap : Computable (toArithmetic p f) :=
    Computable.option_map hdag ((h.2 p hp f hfc hf).1.comp Computable.snd).to₂
  exact ⟨hap,Computable.option_map hap (h.1.comp Computable.snd).to₂⟩

end LogicLineages.ControlSensitivityCurrent.CurrentDecisionTreePresentation
