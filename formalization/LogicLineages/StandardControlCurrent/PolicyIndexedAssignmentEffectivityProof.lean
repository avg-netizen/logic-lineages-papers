module
public import LogicLineages.StandardControlCurrent.PolicyIndexedAssignmentTargets
import LogicLineages.StandardControlCurrent.PolicyIndexedAssignmentConstructorPrograms
import LogicLineages.StandardControlCurrent.PolicyIndexedRankedLayerProof
import LogicLineages.StandardControlCurrent.PolicyIndexedRankedGraphProof
import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckStatementChecks

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedAssignment
open OrdinalComparison Source Source.SyntaxCode
open Nat.Partrec (Code)

abbrev AbstractionArgs := Code × Nat × Nat × List Nat

def AbstractionPartrec (backend : Abstraction) : Prop :=
  Partrec (fun p : AbstractionArgs => backend p.1 p.2.1 p.2.2.1 p.2.2.2)

private theorem rankPrim : Primrec rank := Primrec.snd
private theorem tagPrim : Primrec (fun s : Node => s.2%8) :=
  Primrec.nat_mod.comp rankPrim (Primrec.const 8)
private theorem tagIs (k : Nat) : PrimrecPred (fun s : Node => s.2%8=k) :=
  Primrec.eq.comp tagPrim (Primrec.const k)
private theorem unpackPrim : Primrec (fun s : Node => (s.2/8).unpair) :=
  Primrec.unpair.comp (Primrec.nat_div.comp rankPrim (Primrec.const 8))

private theorem childrenPrim : Primrec children := by
  let l : Node → Node := fun x => (x.1,(x.2/8).unpair.1)
  let r : Node → Node := fun x => (x.1,(x.2/8).unpair.2)
  let b : Node → Node := fun x => ((x.2/8).unpair.1::x.1,(x.2/8).unpair.2)
  have hl : Primrec l := Primrec.fst.pair (Primrec.fst.comp unpackPrim)
  have hr : Primrec r := Primrec.fst.pair (Primrec.snd.comp unpackPrim)
  have hb : Primrec b :=
    (Primrec.list_cons.comp (Primrec.fst.comp unpackPrim) Primrec.fst).pair
      (Primrec.snd.comp unpackPrim)
  exact Primrec.ite (tagIs 5) (Primrec.list_cons.comp hl
    (Primrec.list_cons.comp hr (Primrec.const [])))
    (Primrec.ite (tagIs 6) (Primrec.list_cons.comp hb (Primrec.const [])) (Primrec.const []))

private theorem varPrim : Primrec (fun p : Nat × Nat =>
    (List.range (p.2+1)).map (fun i => 8*Nat.pair p.1 i+3)) :=
  Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
      (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)) (Primrec.const 3)).to₂)

private theorem onesPrim : Primrec (fun n : Nat => List.replicate (n+1) (1 : Nat)) := by
  have h := Primrec.list_map (Primrec.list_range.comp Primrec.succ) (Primrec.const 1).to₂
  exact h.of_eq (by intro n; simp)

private theorem optionPair {T X Y : Type} [Primcodable T] [Primcodable X] [Primcodable Y]
    {f : T → Option X} {g : T → Option Y} (hf : Computable f) (hg : Computable g) :
    Computable (fun p => (f p).bind (fun x => (g p).map (x, ·))) := by
  let Z := T × X
  have hm : Computable₂ (fun (p : Z) (y : Y) => (p.2,y)) :=
    ((Computable.snd.comp Computable.fst).pair Computable.snd).to₂
  exact Computable.option_bind hf (Computable.option_map (hg.comp Computable.fst) hm).to₂

private def reqApp (s : Node) (rs : List Value) : Option (Nat × List Nat × List Nat) := do
  let ty ← check s.1 (s.2/8).unpair.2
  let f ← rs.getD 0 none
  let g ← rs.getD 1 none
  pure (ty,f,g)

private def reqLam (s : Node) (rs : List Value) : Option (Nat × List Nat) := do
  let ty ← check ((s.2/8).unpair.1::s.1) (s.2/8).unpair.2
  let b ← rs.getD 0 none
  pure (ty,b)

private theorem reqAppProgram : Computable₂ reqApp := by
  let T := Args
  have first : Computable (fun p : T => check p.1.1 (p.1.2/8).unpair.2) :=
    SyntaxCode.StatementChecks.checkPrimitiveRecursive.to_comp.comp
      ((Computable.fst.comp Computable.fst).pair
        ((Primrec.snd.comp unpackPrim).to_comp.comp Computable.fst))
  have child (k : Nat) : Computable (fun p : T => p.2.getD k none) :=
    (Primrec.list_getD (none : Value)).to_comp.comp Computable.snd (Computable.const k)
  have h := optionPair first (optionPair (child 0) (child 1))
  have eq : Computable (fun p : T => reqApp p.1 p.2) := h.of_eq (by
    intro p
    unfold reqApp
    cases check p.1.1 (p.1.2/8).unpair.2 <;>
      cases p.2.getD 0 none <;> cases p.2.getD 1 none <;> rfl)
  exact eq.to₂

private theorem reqLamProgram : Computable₂ reqLam := by
  let T := Args
  have hctx : Computable (fun p : T => (p.1.2/8).unpair.1::p.1.1) :=
    Primrec.list_cons.to_comp.comp ((Primrec.fst.comp unpackPrim).to_comp.comp Computable.fst)
      (Computable.fst.comp Computable.fst)
  have checkL := SyntaxCode.StatementChecks.checkPrimitiveRecursive.to_comp.comp
    (hctx.pair ((Primrec.snd.comp unpackPrim).to_comp.comp (Computable.fst : Computable (Prod.fst : T → Node))))
  have val : Computable (fun p : T => p.2.getD 0 none) :=
    (Primrec.list_getD (none : Value)).to_comp.comp Computable.snd (Computable.const 0)
  have h : Computable (fun p : T => reqLam p.1 p.2) := (optionPair checkL val).of_eq (by
    intro p
    unfold reqLam
    cases check ((p.1.2/8).unpair.1::p.1.1) (p.1.2/8).unpair.2 <;>
      cases p.2.getD 0 none <;> rfl)
  exact h.to₂

private theorem assembledBodyPartrec (backend : Abstraction) (ha : AbstractionPartrec backend) :
    Partrec (fun p : Code × Args =>
      body Part.some
        (fun i r => (numeral p.1 2).map (Option.map (recursorFrom i r)))
        (fun r i f g => (tailCode p.1 i (f.getD 0 0) (g.getD 0 0)).map
          (Option.map (applicationFrom r i f g)))
        (backend p.1) p.2.1 p.2.2) := by
  let A := Code × Args
  let E := A × Nat
  have checkMain : Computable (fun p : A => check p.2.1.1 p.2.1.2) :=
    SyntaxCode.StatementChecks.checkPrimitiveRecursive.to_comp.comp (Computable.fst.comp Computable.snd)
  have data : Computable (fun x : E => x.1.2) := Computable.snd.comp Computable.fst
  have getNode : Primrec (fun x : E => x.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have getCode : Computable (fun x : E => x.1.1) := Computable.fst.comp Computable.fst
  have tyLevel : Primrec typeLevel := SyntaxCode.StatementChecks.typeLevelPrimitiveRecursive
  have result : Computable (fun x : E => typeLevel x.2) := tyLevel.to_comp.comp Computable.snd
  have payload : Primrec (fun x : E => x.1.2.1.2/8) :=
    Primrec.nat_div.comp (rankPrim.comp getNode) (Primrec.const 8)
  have getArg : Computable (fun x : E => reqApp x.1.2.1 x.1.2.2) := reqAppProgram.comp
    (Computable.fst.comp data) (Computable.snd.comp data)
  have getBody : Computable (fun x : E => reqLam x.1.2.1 x.1.2.2) := reqLamProgram.comp
    (Computable.fst.comp data) (Computable.snd.comp data)
  have var : Partrec (fun x : E => Part.some (some ((List.range (typeLevel x.2+1)).map
      (fun i => 8*Nat.pair (x.1.2.1.2/8) i+3)))) :=
    (Computable.option_some.comp (varPrim.to_comp.comp (payload.to_comp.pair result))).partrec
  have constant : Partrec (fun x : E => Part.some (some (List.replicate (typeLevel x.2+1) 1))) :=
    (Computable.option_some.comp (onesPrim.to_comp.comp result)).partrec
  have recCode := recursorPartrec.comp (getCode.pair
    ((tyLevel.to_comp.comp payload.to_comp).pair result))
  have appCase : Partrec₂ (fun (x : E) (v : Nat × List Nat × List Nat) =>
      (tailCode x.1.1 (typeLevel v.1) (v.2.1.getD 0 0) (v.2.2.getD 0 0)).map
        (Option.map (applicationFrom (typeLevel x.2) (typeLevel v.1) v.2.1 v.2.2))) :=
    (applicationPartrec.comp ((getCode.comp Computable.fst).pair
      ((result.comp Computable.fst).pair
        ((tyLevel.to_comp.comp (Computable.fst.comp Computable.snd)).pair
          (Computable.snd.comp Computable.snd))))).to₂
  have inputLevel : Computable (fun x : E => typeLevel (x.1.2.1.2/8).unpair.1) :=
    tyLevel.to_comp.comp ((Primrec.fst.comp unpackPrim).comp getNode).to_comp
  have absCase : Partrec₂ (fun (x : E) (v : Nat × List Nat) =>
      backend x.1.1 (typeLevel (x.1.2.1.2/8).unpair.1) (typeLevel v.1) v.2) :=
    (ha.comp ((getCode.comp Computable.fst).pair
      ((inputLevel.comp Computable.fst).pair
        ((tyLevel.to_comp.comp (Computable.fst.comp Computable.snd)).pair
          (Computable.snd.comp Computable.snd))))).to₂
  have app := partialOnSome getArg appCase
  have abs := partialOnSome getBody absCase
  have no : Partrec (fun _ : E => Part.some (none : Value)) := Partrec.const' _
  have lowTag : PrimrecPred (fun x : E => x.1.2.1.2%8<5) :=
    Primrec.nat_lt.comp (tagPrim.comp getNode) (Primrec.const 5)
  have chooseTag (k : Nat) : PrimrecPred (fun x : E => x.1.2.1.2%8=k) := (tagIs k).comp getNode
  have dispatch := partChoose lowTag
    (partChoose (chooseTag 0) var (partChoose (chooseTag 4) recCode constant))
    (partChoose (chooseTag 5) app (partChoose (chooseTag 6) abs no))
  apply (partialOnSome checkMain dispatch.to₂).of_eq
  rintro ⟨c,⟨ctx,n⟩,rs⟩
  cases hmain : check ctx n with
  | none => simp [body,hmain]
  | some ty =>
    by_cases lo : n%8<5
    · by_cases h0 : n%8=0
      · simp [body,hmain,lo,h0]
      · by_cases h4 : n%8=4 <;> simp [body,hmain,lo,h0,h4]
    · by_cases h5 : n%8=5
      · cases harg : check ctx (n/8).unpair.2 <;>
          cases h1 : rs.getD 0 none <;> cases h2 : rs.getD 1 none <;>
          simp [body,reqApp,hmain,lo,h5,harg,h1,h2]
      · by_cases h6 : n%8=6
        · cases hb : check ((n/8).unpair.1::ctx) (n/8).unpair.2 <;>
            cases hv : rs.getD 0 none <;> simp [body,reqLam,hmain,lo,h5,h6,hb,hv]
        · simp [body,hmain,lo,h5,h6]

theorem indexedAssignmentAssemblePartrec (backend : Abstraction) (ha : AbstractionPartrec backend) :
    Partrec₂ (assemble backend) :=
  (Partrec.map (assembledBodyPartrec backend ha) (Computable.option_some.comp Computable.snd).to₂).to₂

theorem indexedAssignmentRunPartrec (backend : Abstraction) (ha : AbstractionPartrec backend) :
    Partrec (run backend) :=
  (PolicyIndexedRankedGraph.policyIndexedRankedEffectivity _ _ _ rank children
    (PolicyIndexedRankedLayer.layer children (assemble backend)) rankPrim childrenPrim
    (PolicyIndexedRankedLayer.indexedLayerEffectivity _ _ _ children (assemble backend)
      childrenPrim (indexedAssignmentAssemblePartrec backend ha))).2

end LogicLineages.StandardControlCurrent.PolicyIndexedAssignment
