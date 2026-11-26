module
public import LogicLineages.PermittedControl.UniformGroundAssemblyTargets
import LogicLineages.PermittedControl.UniformGroundComparisonCloseProof
import LogicLineages.PermittedControl.GroundComparisonAssemblyTargets
import LogicLineages.PermittedControl.GroundComparisonReductionProof
import LogicLineages.PermittedControl.GroundComparisonPositiveProof
import LogicLineages.PermittedControl.SelectedGeneratedSourceProof
import LogicLineages.PermittedControl.StageCallbackGuardRenderCloseProof
import LogicLineages.PermittedControl.GroundScalarCircuitCalibrationProof
import LogicLineages.PermittedControl.GroundScalarCircuitEffectivityProof
import LogicLineages.OrdinalComparison.WWScalarSyntaxCodeProof

public section
namespace LogicLineages.PermittedControl.UniformGroundAssembly
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.ForwardTranslation
open SelectedSourceDomain SelectedGeneratedSource
open GroundComparison (Relation Canonical)
open GroundComparisonPositive (positiveTest positiveTestEffectivity)
open GroundComparisonReduction (idx tagOf equalFlag exactCanonicalReduction)
open GroundComparisonAssembly (QueryInterface)
open ClosedBlockDecision (Decides)
open PolicySuppliedCodeMacro (RealizesPolicy)
open UniformPolicyCompiler (Calibrated)
open UniformGroundComparison (GroundArgs)

attribute [local irreducible] StandardControlCurrent.PolicySourceInterface.compile

private abbrev QArgs := OriginalPrintedRawFamilyFrontend.Args

variable {P : Type} [Primcodable P]

/-- The decision body of the per-policy assembly, with a parameter `t`
passed to the closed-block decider. -/
private def body (cbd : P × QArgs → Option Bool) (query : Nat → Nat → Nat → QArgs) (rel : Relation)
    (t : P) (ea eb : EncodedVector) : Bool :=
  positiveTest (equalFlag rel) ea.2 eb.2 &&
    !(decide (cbd (t,query (tagOf rel) (normalizeScalarSyntaxCode ea.1) (normalizeScalarSyntaxCode eb.1)) =
      some true))

private def combine (cbd : P × QArgs → Option Bool) (query : Nat → Nat → Nat → QArgs) (rel : Relation)
    (t : P) (oa ob : Option EncodedVector) : Bool :=
  (oa.bind (fun ea => ob.map (fun eb => body cbd query rel t ea eb))).getD false

/-- The uniform procedure: compile both terms with the supplied policy
program, then run the fixed decision body. -/
private def run (compilePolicy : Nat.Partrec.Code × Nat × Nat →. Option EncodedVector)
    (cbd : P × QArgs → Option Bool) (query : Nat → Nat → Nat → QArgs) (rel : Relation)
    (x : P × GroundArgs) : Part Bool :=
  (compilePolicy (x.2.1,x.2.2.1,x.2.2.2.1)).bind (fun oa =>
    (compilePolicy (x.2.1,x.2.2.1,x.2.2.2.2)).map (fun ob => combine cbd query rel x.1 oa ob))

private theorem combineComputable (cbd : P × QArgs → Option Bool) (hcbd : Computable cbd)
    (query : Nat → Nat → Nat → QArgs)
    (hq : Computable (fun x : Nat × Nat × Nat => query x.1 x.2.1 x.2.2)) (rel : Relation) :
    Computable (fun w : P × Option EncodedVector × Option EncodedVector =>
      combine cbd query rel w.1 w.2.1 w.2.2) := by
  let Q := P × EncodedVector × EncodedVector
  have norm : Primrec normalizeScalarSyntaxCode := scalarSyntaxNormalizationPrimitiveRecursive
  have pos : Computable (fun q : Q => positiveTest (equalFlag rel) q.2.1.2 q.2.2.2) := by
    have h := positiveTestEffectivity.comp
      ((Primrec.const (equalFlag rel)).pair ((Primrec.snd.comp (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) :
        Primrec (fun q : Q => (equalFlag rel,q.2.1.2,q.2.2.2)))
    exact h.to_comp
  have qArgs : Computable (fun q : Q =>
      (tagOf rel,normalizeScalarSyntaxCode q.2.1.1,normalizeScalarSyntaxCode q.2.2.1)) := by
    have h := (Primrec.const (tagOf rel)).pair
      ((norm.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).pair
        (norm.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))) :
        Primrec (fun q : Q => (normalizeScalarSyntaxCode q.2.1.1,normalizeScalarSyntaxCode q.2.2.1)))
    exact h.to_comp
  have qv : Computable (fun q : Q =>
      query (tagOf rel) (normalizeScalarSyntaxCode q.2.1.1) (normalizeScalarSyntaxCode q.2.2.1)) := by
    have h := hq.comp qArgs
    exact h
  have cv : Computable (fun q : Q =>
      cbd (q.1,query (tagOf rel) (normalizeScalarSyntaxCode q.2.1.1) (normalizeScalarSyntaxCode q.2.2.1))) := by
    have h := hcbd.comp (Computable.pair Computable.fst qv)
    exact h
  have isTrue : Primrec (fun o : Option Bool => decide (o = some true)) :=
    (Primrec.eq.comp Primrec.id (Primrec.const (some true))).decide
  have test := isTrue.to_comp.comp cv
  have neg := Primrec.not.to_comp.comp test
  have hbody : Computable (fun q : Q => body cbd query rel q.1 q.2.1 q.2.2) := by
    have h := Primrec.and.to_comp.comp pos neg
    exact h
  let W := P × Option EncodedVector × Option EncodedVector
  have inner : Computable (fun y : W × EncodedVector =>
      (y.1.2.2).map (fun eb => body cbd query rel y.1.1 y.2 eb)) := by
    have hbz : Computable (fun z : (W × EncodedVector) × EncodedVector =>
        body cbd query rel z.1.1.1 z.1.2 z.2) := by
      have h := hbody.comp (Computable.pair (Computable.fst.comp (Computable.fst.comp Computable.fst))
        (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd) :
          Computable (fun z : (W × EncodedVector) × EncodedVector => ((z.1.1.1,z.1.2,z.2) : Q)))
      exact h
    have hOb : Computable (fun y : W × EncodedVector => y.1.2.2) :=
      Computable.snd.comp (Computable.snd.comp Computable.fst)
    exact Computable.option_map hOb hbz.to₂
  have hOa : Computable (fun w : W => w.2.1) := Computable.fst.comp Computable.snd
  have outer := Computable.option_bind hOa inner.to₂
  have h := Computable.option_getD outer (Computable.const false)
  exact h

private theorem runPartrec (compilePolicy : Nat.Partrec.Code × Nat × Nat →. Option EncodedVector)
    (hpart : Partrec compilePolicy) (cbd : P × QArgs → Option Bool) (hcbd : Computable cbd)
    (query : Nat → Nat → Nat → QArgs)
    (hq : Computable (fun x : Nat × Nat × Nat => query x.1 x.2.1 x.2.2)) (rel : Relation) :
    Partrec (run compilePolicy cbd query rel : P × GroundArgs →. Bool) := by
  let X := P × GroundArgs
  have hA : Partrec (fun x : X => compilePolicy (x.2.1,x.2.2.1,x.2.2.2.1)) := by
    have h := hpart.comp (Computable.pair (Computable.fst.comp Computable.snd)
      (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.snd))
        (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))) :
        Computable (fun x : X => (x.2.1,x.2.2.1,x.2.2.2.1)))
    exact h
  have hB : Partrec (fun y : X × Option EncodedVector =>
      compilePolicy (y.1.2.1,y.1.2.2.1,y.1.2.2.2.2)) := by
    have h := hpart.comp (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
      (Computable.pair (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))))) :
        Computable (fun y : X × Option EncodedVector => (y.1.2.1,y.1.2.2.1,y.1.2.2.2.2)))
    exact h
  have hc := combineComputable cbd hcbd query hq rel
  have step : Computable₂ (fun (y : X × Option EncodedVector) (ob : Option EncodedVector) =>
      combine cbd query rel y.1.1 y.2 ob) := by
    have h := hc.comp (Computable.pair (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd) :
        Computable (fun z : (X × Option EncodedVector) × Option EncodedVector => (z.1.1.1,z.1.2,z.2)))
    exact h.to₂
  have inner : Partrec₂ (fun (x : X) (oa : Option EncodedVector) =>
      (compilePolicy (x.2.1,x.2.2.1,x.2.2.2.2)).map (fun ob => combine cbd query rel x.1 oa ob)) := by
    have h := Partrec.map hB step
    exact h.to₂
  have h := Partrec.bind hA inner
  exact h

/-- One procedure for a whole family of selected controls indexed by `t`,
given a decider for their closed blocks that is computable jointly in `t`. -/
private theorem family (ctrl : P → Nat → Nat) (K : P → Nat)
    (hsel : ∀ t, SelectedWithThreshold (ctrl t) (K t))
    (cbd : P × QArgs → Option Bool) (hcbd : Computable cbd)
    (hdec : ∀ t, Decides (ctrl t) (fun x => cbd (t,x)))
    (compilePolicy : Nat.Partrec.Code × Nat × Nat →. Option EncodedVector)
    (hpart : Partrec compilePolicy) (hcal : Calibrated compilePolicy)
    (query : Nat → Nat → Nat → QArgs) (hq : QueryInterface query)
    (hqc : Computable (fun x : Nat × Nat × Nat => query x.1 x.2.1 x.2.2)) (rel : Relation) :
    ∃ decide : P × GroundArgs →. Bool, Partrec decide ∧
      ∀ (t : P) (e : Nat.Partrec.Code) (p : Policy), RealizesPolicy e p →
        (∀ n ca cb : Nat, (decide (t,e,n,ca,cb)).Dom) ∧
        ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
          ∀ (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ),
            ∃ answer : Bool,
              decide (t,e,Γ.length,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b) = Part.some answer ∧
              (answer = true ↔ Canonical (ctrl t) p rel a b) := by
  refine ⟨run compilePolicy cbd query rel,runPartrec compilePolicy hpart cbd hcbd query hqc rel,?_⟩
  intro t e p realizes
  have value : ∀ n ca cb : Nat, run compilePolicy cbd query rel (t,e,n,ca,cb) =
      Part.some (combine cbd query rel t (StandardControlCurrent.PolicySourceInterface.compile p n ca)
        (StandardControlCurrent.PolicySourceInterface.compile p n cb)) := by
    intro n ca cb
    simp only [run,hcal e p realizes,Part.bind_some,Part.map_some]
  refine ⟨fun n ca cb => by rw [value]; trivial,?_⟩
  intro Γ hΓ τ υ a b
  refine ⟨_,value Γ.length (SyntaxCode.encodeTerm a) (SyntaxCode.encodeTerm b),?_⟩
  obtain ⟨va,ca,ha,_,hca,_,hva,_⟩ :=
    SelectedGeneratedSourceProof.typedImage (ctrl t) (K t) (hsel t) p Γ hΓ τ a
  obtain ⟨vb,cb,hb,_,hcb',_,hvb,_⟩ :=
    SelectedGeneratedSourceProof.typedImage (ctrl t) (K t) (hsel t) p Γ hΓ υ b
  have red := exactCanonicalReduction (ctrl t) (K t) (hsel t) p Γ hΓ τ υ a b va vb ca cb ha hb hva hvb rel
  obtain ⟨known,gs,pf,htop,hplain,hqeq,hsem⟩ :=
    hq (tagOf rel) (fun x : OrdinalComponent Γ => SourceTypedPorts.variableIndex x.2.1) ca.scalar cb.scalar
  have hcbt : cbd (t,OriginalPrintedRawFamilyFrontend.encodeInput known gs pf true) = some true ↔
      OriginalPrintedTypedExistential.HasSuccessfulObservation (ctrl t) gs pf true :=
    (hdec t known gs pf htop hplain true).1
  have na := scalarSyntaxNormalizationCorrect (OrdinalComponent Γ)
    (fun x : OrdinalComponent Γ => SourceTypedPorts.variableIndex x.2.1) ca.scalar
  have nb := scalarSyntaxNormalizationCorrect (OrdinalComponent Γ)
    (fun x : OrdinalComponent Γ => SourceTypedPorts.variableIndex x.2.1) cb.scalar
  have step : combine cbd query rel t
      (StandardControlCurrent.PolicySourceInterface.compile p Γ.length (SyntaxCode.encodeTerm a))
      (StandardControlCurrent.PolicySourceInterface.compile p Γ.length (SyntaxCode.encodeTerm b)) =
      body cbd query rel t (ca.syntaxCode (fun x => SourceTypedPorts.variableIndex x.2.1))
        (cb.syntaxCode (fun x => SourceTypedPorts.variableIndex x.2.1)) := by
    unfold combine
    rw [hca,hcb']
    rfl
  rw [step,red]
  unfold body
  change (positiveTest (equalFlag rel) (List.ofFn (fun j => closedPositiveCode (ca.positive j)))
      (List.ofFn (fun j => closedPositiveCode (cb.positive j))) &&
    !(decide (cbd (t,query (tagOf rel)
      (normalizeScalarSyntaxCode (scalarSyntaxCode (fun x : OrdinalComponent Γ => SourceTypedPorts.variableIndex x.2.1) ca.scalar))
      (normalizeScalarSyntaxCode (scalarSyntaxCode (fun x : OrdinalComponent Γ => SourceTypedPorts.variableIndex x.2.1) cb.scalar))) =
        some true))) = true ↔ _
  rw [na,nb,hqeq,List.map_ofFn,List.map_ofFn,Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,hcbt,
    hsem (ctrl t) (K t) (hsel t)]
  rfl

theorem exactUniformGroundFromPieces : ExactUniformGroundFromPieces := by
  intro compiler near
  obtain ⟨compilePolicy,hpart,hcal⟩ := compiler
  obtain ⟨nearDecide,nearComputable,nearDecides⟩ := near
  obtain ⟨cbd0,hcbd0,hdec0⟩ := StageCallbackGuardRender.closedBlockDecision.1
  have hq : QueryInterface GroundScalarCircuit.queryCode := GroundScalarCircuit.exactQueryCode
  have hqc := GroundScalarCircuit.queryCodeEffectivity.to_comp
  constructor
  · intro rel
    obtain ⟨decide,partrec,spec⟩ := family (P := Unit) (fun _ => factorialControl) (fun _ => 0)
      (fun _ => Or.inl ⟨rfl,rfl⟩) (fun x => cbd0 x.2) (hcbd0.comp Computable.snd) (fun _ => hdec0)
      compilePolicy hpart hcal GroundScalarCircuit.queryCode hq hqc rel
    refine ⟨fun x => decide ((),x),?_,?_⟩
    · have h := partrec.comp (Computable.pair (Computable.const ()) Computable.id :
        Computable (fun x : GroundArgs => (((),x) : Unit × GroundArgs)))
      exact h
    · intro e p realizes
      exact spec () e p realizes
  · intro rel
    exact family (P := Nat) nearControl (fun b => b+1) (fun b => Or.inr ⟨b,rfl,rfl⟩)
      nearDecide nearComputable nearDecides compilePolicy hpart hcal GroundScalarCircuit.queryCode hq hqc rel

theorem exactUniformMainFromPieces : ExactUniformMainFromPieces :=
  fun compiler near =>
    UniformGroundComparison.uniformMainFromGround (exactUniformGroundFromPieces compiler near)

#print axioms exactUniformGroundFromPieces
#print axioms exactUniformMainFromPieces
end LogicLineages.PermittedControl.UniformGroundAssembly
