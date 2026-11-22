module
public import LogicLineages.PermittedControl.GroundComparisonAssemblyTargets
import LogicLineages.PermittedControl.GroundComparisonReductionProof
import LogicLineages.PermittedControl.GroundComparisonPositiveProof
import LogicLineages.PermittedControl.SelectedGeneratedSourceProof
import LogicLineages.PermittedControl.StageCallbackGuardRenderCloseProof
import LogicLineages.OrdinalComparison.WWScalarSyntaxCodeProof

public section
namespace LogicLineages.PermittedControl.GroundComparisonAssembly
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.ForwardTranslation
open SelectedSourceDomain SelectedGeneratedSource
open GroundComparison (Relation Canonical GroundDecidable)
open GroundComparisonPositive (positiveTest positiveTestEffectivity)
open GroundComparisonReduction (idx tagOf equalFlag exactCanonicalReduction)
open ClosedBlockDecision (DecidableClosedBlocks)

attribute [local irreducible] StandardControlCurrent.PolicySourceInterface.compile

/-- The decision body on two compiled syntax codes. -/
private def body (cbd : OriginalPrintedRawFamilyFrontend.Args → Option Bool)
    (query : Nat → Nat → Nat → OriginalPrintedRawFamilyFrontend.Args) (rel : Relation)
    (ea eb : EncodedVector) : Bool :=
  positiveTest (equalFlag rel) ea.2 eb.2 &&
    !(decide (cbd (query (tagOf rel) (normalizeScalarSyntaxCode ea.1) (normalizeScalarSyntaxCode eb.1)) =
      some true))

private def decider (p : Policy) (cbd : OriginalPrintedRawFamilyFrontend.Args → Option Bool)
    (query : Nat → Nat → Nat → OriginalPrintedRawFamilyFrontend.Args) (rel : Relation)
    (x : Nat × Nat × Nat) : Bool :=
  ((StandardControlCurrent.PolicySourceInterface.compile p x.1 x.2.1).bind (fun ea =>
    (StandardControlCurrent.PolicySourceInterface.compile p x.1 x.2.2).map
      (fun eb => body cbd query rel ea eb))).getD false

private theorem deciderComputable (p : Policy) (hp : StandardControlCurrent.PolicyShape.Effective p)
    (cbd : OriginalPrintedRawFamilyFrontend.Args → Option Bool) (hcbd : Computable cbd)
    (query : Nat → Nat → Nat → OriginalPrintedRawFamilyFrontend.Args)
    (hq : Computable (fun x : Nat × Nat × Nat => query x.1 x.2.1 x.2.2)) (rel : Relation) :
    Computable (decider p cbd query rel) := by
  have hc : Computable (fun x : Nat × Nat => StandardControlCurrent.PolicySourceInterface.compile p x.1 x.2) :=
    SelectedGeneratedSourceProof.fullSelectedGeneratedSource.2.2.2.2.1.1 p hp
  let X := Nat × Nat × Nat
  have hA : Computable (fun x : X => StandardControlCurrent.PolicySourceInterface.compile p x.1 x.2.1) := by
    have h := hc.comp (Computable.fst.pair (Computable.fst.comp Computable.snd) : Computable (fun x : X => (x.1,x.2.1)))
    exact h
  have hB : Computable (fun x : X => StandardControlCurrent.PolicySourceInterface.compile p x.1 x.2.2) := by
    have h := hc.comp (Computable.fst.pair (Computable.snd.comp Computable.snd) : Computable (fun x : X => (x.1,x.2.2)))
    exact h
  let Q := EncodedVector × EncodedVector
  have norm : Primrec normalizeScalarSyntaxCode := scalarSyntaxNormalizationPrimitiveRecursive
  have pos : Computable (fun q : Q => positiveTest (equalFlag rel) q.1.2 q.2.2) := by
    have h := positiveTestEffectivity.comp
      ((Primrec.const (equalFlag rel)).pair ((Primrec.snd.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd)) :
        Primrec (fun q : Q => (equalFlag rel,q.1.2,q.2.2)))
    exact h.to_comp
  have qArgs : Computable (fun q : Q => (tagOf rel,normalizeScalarSyntaxCode q.1.1,normalizeScalarSyntaxCode q.2.1)) := by
    have h := (Primrec.const (tagOf rel)).pair ((norm.comp (Primrec.fst.comp Primrec.fst)).pair
      (norm.comp (Primrec.fst.comp Primrec.snd)) : Primrec (fun q : Q => (normalizeScalarSyntaxCode q.1.1,normalizeScalarSyntaxCode q.2.1)))
    exact h.to_comp
  have qv : Computable (fun q : Q => query (tagOf rel) (normalizeScalarSyntaxCode q.1.1) (normalizeScalarSyntaxCode q.2.1)) := by
    have h := hq.comp qArgs
    exact h
  have cv : Computable (fun q : Q => cbd (query (tagOf rel) (normalizeScalarSyntaxCode q.1.1) (normalizeScalarSyntaxCode q.2.1))) :=
    hcbd.comp qv
  have isTrue : Primrec (fun o : Option Bool => decide (o = some true)) :=
    (Primrec.eq.comp Primrec.id (Primrec.const (some true))).decide
  have test := isTrue.to_comp.comp cv
  have neg := Primrec.not.to_comp.comp test
  have hbody : Computable (fun q : Q => body cbd query rel q.1 q.2) := by
    have h := Primrec.and.to_comp.comp pos neg
    exact h
  have inner : Computable (fun y : X × EncodedVector =>
      (StandardControlCurrent.PolicySourceInterface.compile p y.1.1 y.1.2.2).map (fun eb => body cbd query rel y.2 eb)) := by
    have hb2 : Computable₂ (fun ea eb : EncodedVector => body cbd query rel ea eb) := hbody.to₂
    have hbz : Computable (fun z : (X × EncodedVector) × EncodedVector => body cbd query rel z.1.2 z.2) :=
      hb2.comp (Computable.snd.comp Computable.fst) Computable.snd
    have hBy : Computable (fun y : X × EncodedVector =>
        StandardControlCurrent.PolicySourceInterface.compile p y.1.1 y.1.2.2) := hB.comp Computable.fst
    exact Computable.option_map hBy hbz.to₂
  have outer := Computable.option_bind hA inner.to₂
  have h := Computable.option_getD outer (Computable.const false)
  exact h

private theorem groundOf (query : Nat → Nat → Nat → OriginalPrintedRawFamilyFrontend.Args)
    (hq : QueryInterface query) (hqc : Computable (fun x : Nat × Nat × Nat => query x.1 x.2.1 x.2.2))
    (ctrl : Nat → Nat) (K : Nat) (hsel : SelectedWithThreshold ctrl K)
    (hcb : DecidableClosedBlocks ctrl) : GroundDecidable ctrl := by
  intro p hp rel
  obtain ⟨cbd,hcbdc,hdec⟩ := hcb
  refine ⟨decider p cbd query rel,deciderComputable p hp cbd hcbdc query hqc rel,?_⟩
  intro Γ hΓ τ υ a b
  obtain ⟨va,ca,ha,_,hca,_,hva,_⟩ := SelectedGeneratedSourceProof.typedImage ctrl K hsel p Γ hΓ τ a
  obtain ⟨vb,cb,hb,_,hcb',_,hvb,_⟩ := SelectedGeneratedSourceProof.typedImage ctrl K hsel p Γ hΓ υ b
  have red := exactCanonicalReduction ctrl K hsel p Γ hΓ τ υ a b va vb ca cb ha hb hva hvb rel
  obtain ⟨known,gs,pf,htop,hplain,hqeq,hsem⟩ :=
    hq (tagOf rel) (fun x : OrdinalComponent Γ => SourceTypedPorts.variableIndex x.2.1) ca.scalar cb.scalar
  have hcbt := (hdec known gs pf htop hplain true).1
  have na := scalarSyntaxNormalizationCorrect (OrdinalComponent Γ)
    (fun x : OrdinalComponent Γ => SourceTypedPorts.variableIndex x.2.1) ca.scalar
  have nb := scalarSyntaxNormalizationCorrect (OrdinalComponent Γ)
    (fun x : OrdinalComponent Γ => SourceTypedPorts.variableIndex x.2.1) cb.scalar
  have step : decider p cbd query rel (Γ.length,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b) =
      body cbd query rel (ca.syntaxCode (fun x => SourceTypedPorts.variableIndex x.2.1))
        (cb.syntaxCode (fun x => SourceTypedPorts.variableIndex x.2.1)) := by
    unfold decider
    rw [hca,hcb']
    rfl
  rw [step,red]
  unfold body
  change (positiveTest (equalFlag rel) (List.ofFn (fun j => closedPositiveCode (ca.positive j)))
      (List.ofFn (fun j => closedPositiveCode (cb.positive j))) &&
    !(decide (cbd (query (tagOf rel)
      (normalizeScalarSyntaxCode (scalarSyntaxCode (fun x : OrdinalComponent Γ => SourceTypedPorts.variableIndex x.2.1) ca.scalar))
      (normalizeScalarSyntaxCode (scalarSyntaxCode (fun x : OrdinalComponent Γ => SourceTypedPorts.variableIndex x.2.1) cb.scalar))) =
        some true))) = true ↔ _
  rw [na,nb,hqeq,List.map_ofFn,List.map_ofFn,Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,hcbt,
    hsem ctrl K hsel]
  rfl

theorem exactGroundFromQuery : ExactGroundFromQuery := by
  intro query hq hqc
  have cbd := StageCallbackGuardRender.closedBlockDecision
  exact ⟨groundOf query hq hqc _ 0 (Or.inl ⟨rfl,rfl⟩) cbd.1,
    fun b => groundOf query hq hqc _ (b+1) (Or.inr ⟨b,rfl,rfl⟩) (cbd.2 b)⟩

#print axioms exactGroundFromQuery
end LogicLineages.PermittedControl.GroundComparisonAssembly
