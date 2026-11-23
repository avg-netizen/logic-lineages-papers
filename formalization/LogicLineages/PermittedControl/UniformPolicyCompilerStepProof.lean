module
public import LogicLineages.PermittedControl.UniformPolicyCompilerPiecesProof
public import LogicLineages.StandardControlCurrent.PolicyAssignmentDefinitions
import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckStatementChecks
import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeTypesStatementChecks
import LogicLineages.OrdinalComparison.WWOrdinalSyntaxVectorCompilerComputability
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.UniformPolicyCompiler
open OrdinalComparison Source Source.AdmissibleSum Source.SyntaxCode Source.OrdinalSyntax Source.ForwardTranslation
open PolicySuppliedCodeMacro (RealizesPolicy)
open StandardControlCurrent

/-! ## Base codes -/

noncomputable def primeP (e : Code) (tag payload resultLevel : Nat) : Part (Option (List Nat)) :=
  if tag = 0 then Part.some (some ((List.range (resultLevel+1)).map (fun i => 8*Nat.pair payload i+3)))
  else if tag = 4 then recursorP e (typeLevel payload) resultLevel
  else Part.some (some (List.replicate (resultLevel+1) 1))

theorem primePartrec : Partrec (fun x : Code × Nat × Nat × Nat => primeP x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let A := Code × Nat × Nat × Nat
  have ht : Primrec (fun x : A => x.2.1) := Primrec.fst.comp Primrec.snd
  have hp : Primrec (fun x : A => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hr : Primrec (fun x : A => x.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hvars : Primrec (fun x : A => (List.range (x.2.2.2+1)).map (fun i => 8*Nat.pair x.2.2.1 i+3)) := by
    apply Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp hr))
    exact (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
      (Primrec₂.natPair.comp (hp.comp Primrec.fst) Primrec.snd)) (Primrec.const 3)).to₂
  have hones : Primrec (fun x : A => List.replicate (x.2.2.2+1) 1) := by
    have h := Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp hr)) (Primrec.const 1).to₂
    exact h.of_eq (fun x => by simp)
  have hrec : Partrec (fun x : A => recursorP x.1 (typeLevel x.2.2.1) x.2.2.2) := by
    have h := recursorPartrec.comp (Computable.fst.pair
      ((SyntaxCode.StatementChecks.typeLevelPrimitiveRecursive.comp hp).to_comp.pair hr.to_comp))
    exact h
  have h0 : Computable (fun x : A => decide (x.2.1 = 0)) := (Primrec.eq.comp ht (Primrec.const 0)).decide.to_comp
  have h4 : Computable (fun x : A => decide (x.2.1 = 4)) := (Primrec.eq.comp ht (Primrec.const 4)).decide.to_comp
  have h := pite (P := fun x : A => x.2.1 = 0) h0 (Primrec.option_some.comp hvars).to_comp.partrec
    (pite (P := fun x : A => x.2.1 = 4) h4 hrec (Primrec.option_some.comp hones).to_comp.partrec)
  exact h

theorem primeCal {e : Code} {p : Policy} (he : RealizesPolicy e p) (tag payload resultLevel : Nat) :
    primeP e tag payload resultLevel = Part.some (PolicyAssignment.primeCode p tag payload resultLevel) := by
  unfold primeP PolicyAssignment.primeCode
  by_cases h0 : tag = 0
  · simp [h0]
  · rw [if_neg h0,if_neg h0]
    by_cases h4 : tag = 4
    · rw [if_pos h4,if_pos h4]
      exact recursorCal he _ _
    · simp [h4]

/-! ## The assignment recursion through the fixed-point theorem -/

abbrev AArgs := Code × List Nat × Nat

/-- Branch arguments: (program for the recursive call, policy program, context, term code, result type). -/
abbrev BArgs := Code × Code × List Nat × Nat × Nat

private theorem q1P : Primrec (fun n : Nat => (n/8).unpair.1) :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 8)))

private theorem q2P : Primrec (fun n : Nat => (n/8).unpair.2) :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 8)))

private theorem checkP : Primrec (fun p : List Nat × Nat => check p.1 p.2) :=
  SyntaxCode.StatementChecks.checkPrimitiveRecursive

private theorem levelP : Primrec typeLevel := SyntaxCode.StatementChecks.typeLevelPrimitiveRecursive

noncomputable def appInner (G : AArgs →. Option (List Nat)) (e : Code) (Γ : List Nat) (n rt argType : Nat)
    (f : List Nat) : Part (Option (List Nat)) :=
  pbind (G (e,Γ,(n/8).unpair.2)) (fun a => applicationP e (typeLevel rt) (typeLevel argType) f a)

/-- A recursive call through the program followed by a partial continuation. -/
private theorem callBind {A β : Type} [Primcodable A] [Primcodable β]
    {c : A → Code} {u : A → AArgs} {k : A → List Nat →. Option β}
    (hc : Computable c) (hu : Computable u) (hk : Partrec₂ k) :
    Partrec (fun y : A => pbind (decodeEval (c y) (u y) : Part (Option (List Nat))) (k y)) := by
  have h1 : Partrec (fun y : A => (decodeEval (c y) (u y) : Part (Option (List Nat)))) :=
    decodeEvalPartrec.comp (hc.pair hu)
  exact pbindPartrec h1 hk

set_option maxHeartbeats 50000 in
theorem appInnerPartrec : Partrec (fun x : (BArgs × Nat) × List Nat =>
    appInner (decodeEval x.1.1.1) x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1 x.1.1.2.2.2.2 x.1.2 x.2) := by
  let X := (BArgs × Nat) × List Nat
  have hc : Computable (fun x : X => x.1.1.1) := Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hb : Computable (fun x : X => x.1.1.2) := Computable.snd.comp (Computable.fst.comp Computable.fst)
  have he : Computable (fun x : X => x.1.1.2.1) := Computable.fst.comp hb
  have hΓ : Computable (fun x : X => x.1.1.2.2.1) := Computable.fst.comp (Computable.snd.comp hb)
  have hn : Computable (fun x : X => x.1.1.2.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hb))
  have hrt : Computable (fun x : X => x.1.1.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hb))
  have hat : Computable (fun x : X => x.1.2) := Computable.snd.comp Computable.fst
  have hf : Computable (fun x : X => x.2) := Computable.snd
  have hq2 : Computable (fun x : X => (x.1.1.2.2.2.1/8).unpair.2) := q2P.to_comp.comp hn
  have hlr : Computable (fun x : X => typeLevel x.1.1.2.2.2.2) := levelP.to_comp.comp hrt
  have hla : Computable (fun x : X => typeLevel x.1.2) := levelP.to_comp.comp hat
  have happ : Partrec (fun y : X × List Nat =>
      applicationP y.1.1.1.2.1 (typeLevel y.1.1.1.2.2.2.2) (typeLevel y.1.1.2) y.1.2 y.2) := by
    have h := applicationPartrec.comp ((he.comp Computable.fst).pair ((hlr.comp Computable.fst).pair
      ((hla.comp Computable.fst).pair ((hf.comp Computable.fst).pair Computable.snd))))
    exact h
  have h := callBind (c := fun x : X => x.1.1.1)
    (u := fun x : X => (x.1.1.2.1,x.1.1.2.2.1,(x.1.1.2.2.2.1/8).unpair.2))
    (k := fun x a => applicationP x.1.1.2.1 (typeLevel x.1.1.2.2.2.2) (typeLevel x.1.2) x.2 a)
    hc (he.pair (hΓ.pair hq2)) happ.to₂
  exact h

noncomputable def appMid (G : AArgs →. Option (List Nat)) (e : Code) (Γ : List Nat) (n rt argType : Nat) :
    Part (Option (List Nat)) :=
  pbind (G (e,Γ,(n/8).unpair.1)) (fun f => appInner G e Γ n rt argType f)

theorem appMidPartrec : Partrec (fun x : BArgs × Nat =>
    appMid (decodeEval x.1.1) x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 x.1.2.2.2.2 x.2) := by
  let X := BArgs × Nat
  have hc : Computable (fun x : X => x.1.1) := Computable.fst.comp Computable.fst
  have hb : Computable (fun x : X => x.1.2) := Computable.snd.comp Computable.fst
  have he : Computable (fun x : X => x.1.2.1) := Computable.fst.comp hb
  have hΓ : Computable (fun x : X => x.1.2.2.1) := Computable.fst.comp (Computable.snd.comp hb)
  have hn : Computable (fun x : X => x.1.2.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hb))
  have hq1 : Computable (fun x : X => (x.1.2.2.2.1/8).unpair.1) := q1P.to_comp.comp hn
  have h := callBind (c := fun x : X => x.1.1)
    (u := fun x : X => (x.1.2.1,x.1.2.2.1,(x.1.2.2.2.1/8).unpair.1))
    (k := fun x f => appInner (decodeEval x.1.1) x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 x.1.2.2.2.2 x.2 f)
    hc (he.pair (hΓ.pair hq1)) appInnerPartrec.to₂
  exact h

noncomputable def appBranch (G : AArgs →. Option (List Nat)) (e : Code) (Γ : List Nat) (n rt : Nat) :
    Part (Option (List Nat)) :=
  pbind (Part.some (check Γ (n/8).unpair.2)) (fun argType => appMid G e Γ n rt argType)

theorem appBranchPartrec : Partrec (fun x : BArgs =>
    appBranch (decodeEval x.1) x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  have hΓ : Primrec (fun x : BArgs => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hn : Primrec (fun x : BArgs => x.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hck : Partrec (fun x : BArgs => (Part.some (check x.2.2.1 (x.2.2.2.1/8).unpair.2) : Part (Option Nat))) :=
    (checkP.comp (hΓ.pair (q2P.comp hn))).to_comp.partrec
  have h := pbindPartrec hck appMidPartrec.to₂
  exact h

noncomputable def lamInner (G : AArgs →. Option (List Nat)) (e : Code) (Γ : List Nat) (n bodyType : Nat) :
    Part (Option (List Nat)) :=
  pbind (G (e,(n/8).unpair.1 :: Γ,(n/8).unpair.2)) (fun b =>
    abstractionP e (typeLevel (n/8).unpair.1) (typeLevel bodyType) b)

theorem lamInnerPartrec : Partrec (fun x : BArgs × Nat =>
    lamInner (decodeEval x.1.1) x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 x.2) := by
  let X := BArgs × Nat
  have hc : Computable (fun x : X => x.1.1) := Computable.fst.comp Computable.fst
  have hb : Computable (fun x : X => x.1.2) := Computable.snd.comp Computable.fst
  have he : Computable (fun x : X => x.1.2.1) := Computable.fst.comp hb
  have hΓ : Computable (fun x : X => x.1.2.2.1) := Computable.fst.comp (Computable.snd.comp hb)
  have hn : Computable (fun x : X => x.1.2.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hb))
  have hq1 : Computable (fun x : X => (x.1.2.2.2.1/8).unpair.1) := q1P.to_comp.comp hn
  have hq2 : Computable (fun x : X => (x.1.2.2.2.1/8).unpair.2) := q2P.to_comp.comp hn
  have hctx : Computable (fun x : X => (x.1.2.2.2.1/8).unpair.1 :: x.1.2.2.1) :=
    Primrec.list_cons.to_comp.comp hq1 hΓ
  have hl1 : Computable (fun x : X => typeLevel (x.1.2.2.2.1/8).unpair.1) := levelP.to_comp.comp hq1
  have hlb : Computable (fun x : X => typeLevel x.2) := levelP.to_comp.comp Computable.snd
  have habs : Partrec (fun y : X × List Nat =>
      abstractionP y.1.1.2.1 (typeLevel (y.1.1.2.2.2.1/8).unpair.1) (typeLevel y.1.2) y.2) := by
    have h := abstractionPartrec.comp ((he.comp Computable.fst).pair ((hl1.comp Computable.fst).pair
      ((hlb.comp Computable.fst).pair Computable.snd)))
    exact h
  have h := callBind (c := fun x : X => x.1.1)
    (u := fun x : X => (x.1.2.1,(x.1.2.2.2.1/8).unpair.1 :: x.1.2.2.1,(x.1.2.2.2.1/8).unpair.2))
    (k := fun x b => abstractionP x.1.2.1 (typeLevel (x.1.2.2.2.1/8).unpair.1) (typeLevel x.2) b)
    hc (he.pair (hctx.pair hq2)) habs.to₂
  exact h

noncomputable def lamBranch (G : AArgs →. Option (List Nat)) (e : Code) (Γ : List Nat) (n : Nat) :
    Part (Option (List Nat)) :=
  pbind (Part.some (check ((n/8).unpair.1 :: Γ) (n/8).unpair.2)) (fun bodyType => lamInner G e Γ n bodyType)

theorem lamBranchPartrec : Partrec (fun x : BArgs => lamBranch (decodeEval x.1) x.2.1 x.2.2.1 x.2.2.2.1) := by
  have hΓ : Primrec (fun x : BArgs => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hn : Primrec (fun x : BArgs => x.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hck : Partrec (fun x : BArgs => (Part.some (check ((x.2.2.2.1/8).unpair.1 :: x.2.2.1)
      (x.2.2.2.1/8).unpair.2) : Part (Option Nat))) :=
    (checkP.comp ((Primrec.list_cons.comp (q1P.comp hn) hΓ).pair (q2P.comp hn))).to_comp.partrec
  have h := pbindPartrec hck lamInnerPartrec.to₂
  exact h

noncomputable def contBranch (G : AArgs →. Option (List Nat)) (e : Code) (Γ : List Nat) (n rt : Nat) :
    Part (Option (List Nat)) :=
  if n % 8 < 5 then primeP e (n % 8) (n/8) (typeLevel rt)
  else if n % 8 = 5 then appBranch G e Γ n rt
  else if n % 8 = 6 then lamBranch G e Γ n
  else Part.some none

theorem contBranchPartrec : Partrec (fun x : BArgs =>
    contBranch (decodeEval x.1) x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  have he : Computable (fun x : BArgs => x.2.1) := Computable.fst.comp Computable.snd
  have hn : Primrec (fun x : BArgs => x.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hrt : Primrec (fun x : BArgs => x.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hm : Primrec (fun x : BArgs => x.2.2.2.1 % 8) := Primrec.nat_mod.comp hn (Primrec.const 8)
  have hprime : Partrec (fun x : BArgs => primeP x.2.1 (x.2.2.2.1 % 8) (x.2.2.2.1/8) (typeLevel x.2.2.2.2)) := by
    have h := primePartrec.comp (he.pair (hm.to_comp.pair
      ((Primrec.nat_div.comp hn (Primrec.const 8)).to_comp.pair (levelP.comp hrt).to_comp)))
    exact h
  have hlt : Computable (fun x : BArgs => decide (x.2.2.2.1 % 8 < 5)) :=
    (Primrec.nat_lt.comp hm (Primrec.const 5)).decide.to_comp
  have h5 : Computable (fun x : BArgs => decide (x.2.2.2.1 % 8 = 5)) :=
    (Primrec.eq.comp hm (Primrec.const 5)).decide.to_comp
  have h6 : Computable (fun x : BArgs => decide (x.2.2.2.1 % 8 = 6)) :=
    (Primrec.eq.comp hm (Primrec.const 6)).decide.to_comp
  have hnone : Partrec (fun _ : BArgs => (Part.some none : Part (Option (List Nat)))) :=
    (Computable.const (none : Option (List Nat))).partrec
  have h := pite (P := fun x : BArgs => x.2.2.2.1 % 8 < 5) hlt hprime
    (pite (P := fun x : BArgs => x.2.2.2.1 % 8 = 5) h5 appBranchPartrec
      (pite (P := fun x : BArgs => x.2.2.2.1 % 8 = 6) h6 lamBranchPartrec hnone))
  exact h

noncomputable def assignStep (G : AArgs →. Option (List Nat)) (x : AArgs) : Part (Option (List Nat)) :=
  pbind (Part.some (check x.2.1 x.2.2)) (fun rt => contBranch G x.1 x.2.1 x.2.2 rt)

private theorem contAt {A : Type} [Primcodable A] {c e : A → Code} {Γ : A → List Nat} {n : A → Nat}
    (hc : Computable c) (he : Computable e) (hΓ : Computable Γ) (hn : Computable n) :
    Partrec₂ (fun (a : A) (rt : Nat) => contBranch (decodeEval (c a)) (e a) (Γ a) (n a) rt) := by
  have h := contBranchPartrec.comp ((hc.comp Computable.fst).pair ((he.comp Computable.fst).pair
    ((hΓ.comp Computable.fst).pair ((hn.comp Computable.fst).pair Computable.snd))))
  exact h.to₂

private theorem stepAt {A : Type} [Primcodable A] {c e : A → Code} {Γ : A → List Nat} {n : A → Nat}
    (hc : Computable c) (he : Computable e) (hΓ : Primrec Γ) (hn : Primrec n) :
    Partrec (fun a : A => pbind (Part.some (check (Γ a) (n a)))
      (fun rt => contBranch (decodeEval (c a)) (e a) (Γ a) (n a) rt)) := by
  have hfirst : Partrec (fun a : A => (Part.some (check (Γ a) (n a)) : Part (Option Nat))) :=
    (checkP.comp (hΓ.pair hn)).to_comp.partrec
  exact pbindPartrec hfirst (contAt hc he hΓ.to_comp hn.to_comp)

set_option maxHeartbeats 50000 in
theorem assignStepPartrec : Partrec (fun y : Code × AArgs => assignStep (decodeEval y.1) y.2) :=
  stepAt (A := Code × AArgs) Computable.fst (Computable.fst.comp Computable.snd)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

end LogicLineages.PermittedControl.UniformPolicyCompiler
