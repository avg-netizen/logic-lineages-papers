module
public import LogicLineages.PermittedControl.PolicyIndexedGroundDriverTargets
import LogicLineages.PermittedControl.GroundComparisonPositiveProof
import LogicLineages.OrdinalComparison.WWScalarSyntaxCodeProof

public section
namespace LogicLineages.PermittedControl.PolicyIndexedGroundDriver
open OrdinalComparison Source Source.ForwardTranslation
open GroundComparison (Relation)
open GroundComparisonPositive (positiveTest positiveTestEffectivity)
open GroundComparisonReduction (tagOf equalFlag)

attribute [local irreducible] StandardControlCurrent.PolicySourceInterface.compile

private theorem bodyComputable (cbd : Block) (hcbd : Computable cbd)
    (query : Query) (hq : Computable (fun x : TermInput => query x.1 x.2.1 x.2.2))
    (rel : Relation) : Computable (fun q : EncodedVector × EncodedVector => body cbd query rel q.1 q.2) := by
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
  exact hbody

private def leftArgs (x : IndexedInput) : SourceInput := (x.1,x.2.1,x.2.2.1)
private def rightArgs (x : IndexedInput) : SourceInput := (x.1,x.2.1,x.2.2.2)

private theorem leftArgsComputable : Computable leftArgs := by
  have d : Computable (fun x : IndexedInput => x.2.1) := Computable.fst.comp Computable.snd
  have a : Computable (fun x : IndexedInput => x.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  exact Computable.fst.pair (d.pair a)

private theorem rightArgsComputable : Computable rightArgs := by
  have d : Computable (fun x : IndexedInput => x.2.1) := Computable.fst.comp Computable.snd
  have b : Computable (fun x : IndexedInput => x.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  exact Computable.fst.pair (d.pair b)

private noncomputable def rightDecision (s : IndexedSource) (cbd : Block) (query : Query)
    (rel : Relation) (p : IndexedInput × EncodedVector) : Part Bool :=
  (s (rightArgs p.1)).map (fun ob => (ob.map (fun eb => body cbd query rel p.2 eb)).getD false)

private theorem rightDecisionPartrec (s : IndexedSource) (hs : Partrec s)
    (cbd : Block) (hcbd : Computable cbd) (query : Query)
    (hq : Computable (fun x : TermInput => query x.1 x.2.1 x.2.2)) (rel : Relation) :
    Partrec (rightDecision s cbd query rel) := by
  let R := IndexedInput × EncodedVector
  let Q := R × Option EncodedVector
  have readB : Partrec (fun x : R => s (rightArgs x.1)) :=
    hs.comp (rightArgsComputable.comp Computable.fst)
  have effective := (bodyComputable cbd hcbd query hq rel).to₂
  have applyBody : Computable₂ (fun (x : Q) (eb : EncodedVector) =>
      body cbd query rel x.1.2 eb) := by
    exact (effective.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
      Computable.snd).to₂
  have result : Computable (fun x : Q => (x.2.map (fun eb => body cbd query rel x.1.2 eb)).getD false) :=
    Computable.option_getD (Computable.option_map Computable.snd applyBody) (Computable.const false)
  exact Partrec.map readB result.to₂

theorem indexedDecisionPartrec : IndexedDecisionPartrec := by
  intro s hs cbd hcbd query hq rel
  let Q := IndexedInput × Option EncodedVector
  have readA : Partrec (fun x : IndexedInput => s (leftArgs x)) :=
    hs.comp leftArgsComputable
  have readSecond : Partrec₂ (fun x : Q => fun ea : EncodedVector =>
      rightDecision s cbd query rel (x.1,ea)) := by
    have hb := rightDecisionPartrec s hs cbd hcbd query hq rel
    exact (hb.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)).to₂
  have step : Partrec (fun x : Q =>
      x.2.casesOn (Part.some false) (fun ea => rightDecision s cbd query rel (x.1,ea))) :=
    Partrec.optionCasesOn_right Computable.snd (Computable.const false) readSecond
  have hp := Partrec.bind readA step.to₂
  apply hp.of_eq
  intro x
  change ((s (leftArgs x)).bind (fun o =>
    o.casesOn (Part.some false) (fun ea => rightDecision s cbd query rel (x,ea)))) =
      indexedDecision s cbd query rel x
  rfl

#print axioms indexedDecisionPartrec
end LogicLineages.PermittedControl.PolicyIndexedGroundDriver
