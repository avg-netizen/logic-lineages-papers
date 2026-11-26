module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport (constant arityOf sameOf)
open NumberedMultisetNumeric
/-- role=0 is a term; role=1 an argument list (canonical expectedType=0).
Unknown roles remain total data and carry no typing assertion. -/
def jobNumber (role typ rawJob : Nat) := Nat.pair role (Nat.pair typ rawJob)
def forgetNumber (job : Nat) := (Nat.unpair (Nat.unpair job).2).2
def forget : Program 1 := rightOf (rightOf (.projection 0))
/-- [index,role,expectedType,parentRaw]. -/
def parentTag : Program 4 := leftOf (.projection 3)
def domain : Program 4 := leftOf (rightOf (.projection 3))
def termAnnotation (typ : Program 4) : Program 4 := pairOf (constant 4 0) typ
def listAnnotation : Program 4 := pairOf (constant 4 1) (constant 4 0)
def inherited : Program 4 := pairOf (.projection 1) (.projection 2)
def childAnnotation : Program 4 :=
  OriginalTypedDecoder.ifSame parentTag (constant 4 1)
    (termAnnotation (.composition InternalListCodec.tailCode (fun _ : Fin 1 => .projection 2)))
  (OriginalTypedDecoder.ifSame parentTag (constant 4 2)
    (InternalAcceptance.branch (.projection 0)
      (termAnnotation (consOf domain (.projection 2))) (termAnnotation domain))
  (OriginalTypedDecoder.ifSame parentTag (constant 4 4) listAnnotation
  (OriginalTypedDecoder.ifSame parentTag (constant 4 5) listAnnotation
  (OriginalTypedDecoder.ifSame parentTag (constant 4 7)
    (InternalAcceptance.branch (.projection 0) (termAnnotation domain) listAnnotation) inherited))))
def annotation : Program 4 := InternalAcceptance.branch
  (.composition InternalLessThan.ltTest ![.projection 0,arityOf (.projection 3)])
  inherited childAnnotation
/-- [index,role,expectedType,parentRaw,rawJob]. The raw job is copied unchanged. -/
def decorate : Program 5 :=
  let a : Program 5 := .composition annotation ![.projection 0,.projection 1,.projection 2,.projection 3]
  pairOf (leftOf a) (pairOf (rightOf a) (.projection 4))
/-- [index,old row,role,type,parentRaw,raw job list]. -/
def scanStep : Program 6 :=
  .composition InternalApplicationValidityStackAppend.append
    ![.projection 1,consOf (.composition decorate
      ![.projection 0,.projection 2,.projection 3,.projection 4,
        .composition InternalRawListRecursion.lookup ![.projection 0,.projection 5]]) (constant 6 0)]
def scan : Program 5 := .recursion (constant 4 0) scanStep
/-- [role,type,parentRaw,raw job list]. -/
def decorateAll : Program 4 := .composition scan
  ![.composition OriginalContextInsertion.length (fun _ : Fin 1 => .projection 3),
    .projection 0,.projection 1,.projection 2,.projection 3]
def originalJob : Program 1 := rightOf (rightOf (.projection 0))
def expansion : Program 1 := .composition decorateAll
  ![leftOf (.projection 0),leftOf (rightOf (.projection 0)),leftOf originalJob,
    .composition OriginalHereditaryExpansion.expansion ![leftOf originalJob,rightOf originalJob]]
def annotationValue (k role typ raw : Nat) : Nat × Nat :=
  let tag := (Nat.unpair raw).1
  let dom := (Nat.unpair (Nat.unpair raw).2).1
  if k < OriginalRawSyntaxTransport.arityValue raw then
    if tag = 1 then (0,(Nat.unpair (typ-1)).2)
    else if tag = 2 then (0,if k=0 then 1+Nat.pair dom typ else dom)
    else if tag = 4 ∨ tag = 5 then (1,0)
    else if tag = 7 then (if k=0 then (0,dom) else (1,0))
    else (role,typ)
  else (role,typ)
def decoratedValue (k role typ raw job : Nat) :=
  let a := annotationValue k role typ raw
  jobNumber a.1 a.2 job
/-- Literal bounded numeric lookup order, including duplicate jobs. -/
def values (role typ raw : Nat) (jobs : List Nat) : List Nat :=
  (List.range jobs.length).map (fun k => decoratedValue k role typ raw (jobs[k]?.getD 0))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansion
