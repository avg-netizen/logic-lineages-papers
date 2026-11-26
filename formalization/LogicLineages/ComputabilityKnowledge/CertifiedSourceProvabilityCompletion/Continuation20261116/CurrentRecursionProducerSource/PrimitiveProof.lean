module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.PrimitiveProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115

def stepTags {arity k m : Nat} {p : Program arity} {installed : Formula 1} {lhs rhs : Term 1} {t : Term k}
 {old a : Program 1} {x : Program 3}
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (base : Program m) (qTag GTag : Nat) : CurrentRecursionStepProgram.Tags :=
 {ptag := I.currentK.ptag, ctag := I.currentK.ctag, atag := I.currentK.atag,
  ntag := I.previous.previous.previous.previous.previous.numeralTag,
  mtag := I.previous.previous.previous.previous.previous.mpTag,
  r12 := I.previous.current.constructorTag,r13 := I.previous.previous.current.constructorTag,
  ktag := I.currentK.constructorTag,stag := I.currentS.constructorTag,
  reflexivityTag := I.previous.previous.previous.previous.previous.reflexivityTag,
  qtag := qTag,stepTag := qTag+GorbowPRChildTags.stepTag base,childTag := GTag}
def baseTags {arity k m : Nat} {p : Program arity} {installed : Formula 1} {lhs rhs : Term 1} {t : Term k}
 {old a : Program 1} {x : Program 3}
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (base : Program m) (qTag BTag : Nat) : CurrentRecursionBaseProgram.Tags :=
 {ptag := I.currentK.ptag,ctag := I.currentK.ctag,atag := I.currentK.atag,
  ntag := I.previous.previous.previous.previous.previous.numeralTag,
  mtag := I.previous.previous.previous.previous.previous.mpTag,
  r12 := I.previous.current.constructorTag,r13 := I.previous.previous.current.constructorTag,
  baseTag := qTag+1,childTag := BTag}

theorem stepInstalled {arity k m : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (base : Program m) (step : Program (m+2)) (G : Program (m+3)) (qTag GTag : Nat)
 (hq : (nodes p)[qTag]? = some ⟨m+1,.recursion base step⟩)
 (hs : (nodes p)[qTag+GorbowPRChildTags.stepTag base]? = some ⟨m+2,step⟩)
 (hG : (nodes p)[GTag]? = some ⟨m+3,G⟩) :
 CurrentRecursionStepProgram.Installation p base step G (stepTags I base qTag GTag) :=
 {hp := I.currentK.h_ptag,hc := I.currentK.h_ctag,ha := I.currentK.h_atag,
  hn := I.previous.previous.previous.previous.previous.hnumeral,
  hm := I.previous.previous.previous.previous.previous.hmp,
  h12 := I.previous.current.h_constructor,h13 := I.previous.previous.current.h_constructor,
  hk := I.currentK.h_constructorTag,hs := I.currentS.h_constructorTag,
  hr := I.previous.previous.previous.previous.previous.hreflexivity,
  hq := hq,hstep := hs,hchild := hG}

theorem baseInstalled {arity k m : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (base : Program m) (B : Program (m+1)) (qTag BTag : Nat)
 (hb : (nodes p)[qTag+1]? = some ⟨m,base⟩) (hB : (nodes p)[BTag]? = some ⟨m+1,B⟩) :
 CurrentRecursionBaseProgram.Installation p base B (baseTags I base qTag BTag) :=
 {hp := I.currentK.h_ptag,hc := I.currentK.h_ctag,ha := I.currentK.h_atag,
  hn := I.previous.previous.previous.previous.previous.hnumeral,
  hm := I.previous.previous.previous.previous.previous.hmp,
  h12 := I.previous.current.h_constructor,h13 := I.previous.previous.current.h_constructor,
  hb := hb,hchild := hB}
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.PrimitiveProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.PrimitiveProof
