module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphTemplateProgramsProof
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphUnitBuildProgramsProof
public import LogicLineages.ControlSensitivityCurrent.CurrentCompilerStatementChecks
public import LogicLineages.StandardControlCurrent.ComputableFoldProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open StandardControlCurrent AdmissibleSum
open UnitCode (Block)

private theorem mapProgram {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]
    {xs : α→List β} {f : α→β→γ} (h₁ : Computable xs)
    (h₂ : Computable (fun q : α×β => f q.1 q.2)) :
    Computable (fun q => (xs q).map (f q)) := by
  have h := ComputableFoldProof.filterMapProgram (g := fun a b => some (f a b)) h₁
    (Computable.option_some_iff.mpr h₂)
  simpa only [List.filterMap_eq_map'] using h

private theorem smallProgram (f : Nat→Nat) (hf : Computable f) :
    Computable (fun _ : Nat => smallValues f) := by
  apply mapProgram (xs:=fun _ : Nat => List.range 4) (f:=fun _ n => f n)
  · exact Computable.const _
  · exact hf.comp Computable.snd

private theorem normProgram : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive

attribute [local irreducible] rawNormCode valueCode

set_option maxHeartbeats 400000 in
private theorem pointProgram (f : Nat→Nat) (hc : Computable f) (hf : FullAddition.Targets.SourceGrowth f) :
    Computable (fun q : Nat×Nat => pointValuesCode f q.1 q.2) := by
  let P := Nat×Nat
  have n : Primrec (fun q : P => rawNormCode q.1) := normProgram.comp Primrec.fst
  have c := Primrec.nat_max.comp n (Primrec.snd : Primrec fun q : P => q.2)
  have xs : Primrec (fun q : P => List.range (max (rawNormCode q.1) q.2-rawNormCode q.1)) :=
    Primrec.list_range.comp (Primrec.nat_sub.comp c n)
  let Q := P×Nat
  have a : Primrec (fun q : Q => q.1.1) := Primrec.fst.comp Primrec.fst
  have b : Primrec (fun q : Q => rawNormCode q.1.1+q.2) := Primrec.nat_add.comp (normProgram.comp a) Primrec.snd
  have callback : Computable (fun q : Q => valueCode f q.1.1 (rawNormCode q.1.1+q.2)) :=
    (valueProgram f hc hf).comp (a.pair b).to_comp
  unfold pointValuesCode
  exact mapProgram (xs := fun q : P => List.range (max (rawNormCode q.1) q.2-rawNormCode q.1))
    (f := fun (q : P) i => valueCode f q.1 (rawNormCode q.1+i)) xs.to_comp callback

private abbrev FreshInput := List Nat×Nat
private abbrev Loaded := KInput×ParameterCode
private abbrev RayLoaded := Loaded×FreshInput
private abbrev Runout := Block×Nat

private noncomputable def buildDirect (f : Nat→Nat) (q : RayLoaded×Block) : Runout :=
  let data := q.1.1.2
  let n := rawNormCode data.2.1
  let base := rawNormCode data.1+data.2.2+1
  (directBlock (groundCount q.1.2.1.tail) q.2 q.1.1.1.2.2 n base (smallValues f)
    (pointValuesCode f data.2.1 base),n)

private theorem buildDirectProgram (f : Nat→Nat) (hc : Computable f) (hf : FullAddition.Targets.SourceGrowth f) :
    Computable (buildDirect f) := by
  let Q := RayLoaded×Block
  have D : Primrec (fun q : Q => q.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have Γ : Primrec (fun q : Q => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have k : Primrec (fun q : Q => q.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have δ := Primrec.snd.comp (Primrec.snd.comp k)
  have β := Primrec.fst.comp D
  have ξ := Primrec.fst.comp (Primrec.snd.comp D)
  have c := Primrec.snd.comp (Primrec.snd.comp D)
  have hbase := Primrec.succ.comp (Primrec.nat_add.comp (normProgram.comp β) c)
  have n := normProgram.comp ξ
  have g := countProgram.comp (Primrec.list_tail.comp Γ)
  have sm : Computable (fun _ : Q => smallValues f) := (smallProgram f hc).comp (Computable.const 0)
  have pref := (pointProgram f hc hf).comp (ξ.pair hbase).to_comp
  have fullArg := g.to_comp.pair (Computable.snd.pair (δ.to_comp.pair (n.to_comp.pair
    (hbase.to_comp.pair (sm.pair pref)))))
  exact (directBlockProgram.comp fullArg).pair n.to_comp

private noncomputable def fromRay (p : Policy) (f : Nat→Nat) (q : RayLoaded) : Option Runout :=
  (UnitCode.block p f q.2.1 q.2.2).map fun a => buildDirect f (q,a)

private theorem fromRayProgram (p : Policy) (hp : PolicyShape.Effective p) (f : Nat→Nat)
    (hc : Computable f) (hf : FullAddition.Targets.SourceGrowth f) : Computable (fromRay p f) := by
  have h := (UnitCode.blockProgram p hp f hc hf).comp (Computable.snd : Computable fun q : RayLoaded => q.2)
  exact Computable.option_map h (buildDirectProgram f hc hf).to₂

private noncomputable def prepareDirect (p : Policy) (f : Nat→Nat) (q : Loaded) : Option Runout :=
  (auxiliaryCode q.1.1 q.1.2.1).bind fun a => fromRay p f (q,a)

private theorem prepareDirectProgram (p : Policy) (hp : PolicyShape.Effective p) (f : Nat→Nat)
    (hc : Computable f) (hf : FullAddition.Targets.SourceGrowth f) : Computable (prepareDirect p f) := by
  have k : Primrec (fun q : Loaded => (q.1.1,q.1.2.1)) := (Primrec.fst.comp Primrec.fst).pair
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have h := effectivePrefixData.1.comp k.to_comp
  exact Computable.option_bind h (fromRayProgram p hp f hc hf).to₂

private theorem directPacketProgram (p : Policy) (hp : PolicyShape.Effective p) (f : Nat→Nat)
    (hc : Computable f) (hf : FullAddition.Targets.SourceGrowth f) : Computable (directPacket p f) := by
  have h := (effectivePrefixData.2 p hp f hc hf).1
  apply (Computable.option_bind h (prepareDirectProgram p hp f hc hf).to₂).of_eq
  rintro ⟨Γ,src,δ⟩
  simp only [prepareDirect,fromRay,buildDirect,directPacket,Option.map_eq_bind,bind,pure]
  rfl

private abbrev Selected := OriginalInput×Nat
private abbrev WithB := Selected×Block
private abbrev WithBC := WithB×Block
private abbrev All := WithBC×Runout

private noncomputable def insertFinish (q : All) : Block :=
  insertedBlock (groundCount q.1.1.1.1.1) q.2.2 (SyntaxCode.typeLevel q.1.1.1.2)
    q.1.1.2 q.1.2 q.2.1

attribute [local irreducible] insertedBlock groundCount UnitCode.block directPacket

set_option maxHeartbeats 400000 in
private theorem insertFinishProgram : Computable insertFinish := by
  have h : Primrec (fun q : All => q.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have g := countProgram.comp (Primrec.fst.comp (Primrec.fst.comp h))
  have n := Primrec.snd.comp (Primrec.snd : Primrec (fun q : All => q.2))
  have level := SyntaxCode.Proof.typeLevelPrimitiveRecursive.comp (Primrec.snd.comp h)
  have B := Primrec.snd.comp (Primrec.fst.comp (Primrec.fst : Primrec (fun q : All => q.1)))
  have C := Primrec.snd.comp (Primrec.fst : Primrec (fun q : All => q.1))
  have G := Primrec.fst.comp (Primrec.snd : Primrec (fun q : All => q.2))
  unfold insertFinish
  exact insertedBlockProgram.comp (g.pair (n.pair (level.pair (B.pair (C.pair G))))).to_comp

set_option maxHeartbeats 400000 in
private theorem insertProgram (p : Policy) (hp : PolicyShape.Effective p) (f : Nat→Nat)
    (hc : Computable f) (hf : FullAddition.Targets.SourceGrowth f) : Computable (insertCode p f) := by
  have rawC : Primrec (fun q : OriginalInput => (q.1,q.2.2.1)) :=
    Primrec.fst.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hσ := SyntaxCode.StatementChecks.checkPrimitiveRecursive.comp rawC
  have hblock := UnitCode.blockProgram p hp f hc hf
  have hB : Computable (fun q : Selected => UnitCode.block p f q.1.1 q.1.2.1) :=
    hblock.comp (((Primrec.fst.comp Primrec.fst).pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).to_comp)
  have hC : Computable (fun q : WithB => UnitCode.block p f q.1.1.1 q.1.1.2.2.1) :=
    hblock.comp (rawC.comp (Primrec.fst.comp Primrec.fst)).to_comp
  have k : Primrec (fun q : WithBC => q.1.1.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  have hG := (directPacketProgram p hp f hc hf).comp k.to_comp
  have h := Computable.option_bind hσ.to_comp
    (Computable.option_bind hB (Computable.option_bind hC
      (Computable.option_map hG insertFinishProgram.to₂).to₂).to₂).to₂
  apply h.of_eq
  intro q
  simp only [insertCode,insertFinish,Option.map_eq_bind,bind,pure]
  rcases q with ⟨Γ,B,C,k⟩
  rfl

private theorem compilerFiberProgram : Computable (fun d : Block×List Nat => compiledFiberCode d.1 d.2) := by
  let D := Block×List Nat
  have w : Primrec (fun q : D => q.1.1) := Primrec.fst.comp Primrec.fst
  have m : Primrec (fun q : D => q.1.2) := Primrec.snd.comp Primrec.fst
  have v : Primrec (fun q : D => q.2) := Primrec.snd
  have n := Primrec.nat_add.comp w (Primrec.list_length.comp v)
  have pins := pinProgram.comp w v
  have h := MatrixCode.inputCodeProgram.comp (andProgram.comp m pins).to_comp
  exact CurrentCompiler.StatementChecks.fixed_complete_compiler.1.2.comp (n.to_comp.pair h)

theorem effectiveHeadGraph : Targets.EffectiveHeadGraph := by
  refine ⟨compilerFiberProgram,?_⟩
  intro p hp f hc hf
  exact ⟨Computable.option_map (directPacketProgram p hp f hc hf)
    (Computable.fst.comp Computable.snd).to₂,insertProgram p hp f hc hf⟩

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
