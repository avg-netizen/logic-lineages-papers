module
public import LogicLineages.PermittedControl.ActualRawCanonicalNodeTargets
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingCodePrimitiveProof
import LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadataPrimitiveProof
import LogicLineages.PermittedControl.ActualRawCanonicalNodeCoefficientPrimitiveProof
import LogicLineages.PermittedControl.ActualRawCanonicalNodeDecoratorPrimitiveProof
import LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessorPrimitiveProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalNode
open ActualCanonicalOperandGrouping (RawTerm groupCheckedRaw)
open ActualCanonicalOperandGroupingCode (groupCheckedRawPrimitive)
open ActualRawSignedStaticCeiling (RawSyntax)
open ActualRawCanonicalNodeMetadata (classFlagsCode classFlagsPrimitive)
open ActualRawCanonicalNodeCoefficient (coefficientCode coefficientPrimitive)
open ActualRawCanonicalNodeDecorator (RawMarked decorateCode decoratePrimitive)
open ActualRawMarkedZeroSuccessor (markedSuccessorCode exactRawMarkedSuccessorEffectivity)

private def decorationArgs (p : GroupedArgs) : List RawTerm × List Bool :=
  (p.2.1,classFlagsCode p.2.1 p.2.2)

private theorem decorationArgsPrimitive : Primrec decorationArgs := by
  have tape : Primrec (fun p : GroupedArgs => p.2.1) := Primrec.fst.comp Primrec.snd
  have answers : Primrec (fun p : GroupedArgs => p.2.2) := Primrec.snd.comp Primrec.snd
  exact tape.pair (classFlagsPrimitive.comp tape answers)

private def decorateAt (p : GroupedArgs) : Option (List RawMarked) :=
  decorateCode (decorationArgs p).1 (decorationArgs p).2

private theorem decorateAtPrimitive : Primrec decorateAt :=
  decoratePrimitive.comp (Primrec.fst.comp decorationArgsPrimitive)
    (Primrec.snd.comp decorationArgsPrimitive)

private def bodyArgs (p : GroupedArgs × List RawMarked) : Int × List RawMarked :=
  (p.1.1,p.2)

private theorem bodyArgsPrimitive : Primrec bodyArgs :=
  (Primrec.fst.comp Primrec.fst).pair Primrec.snd

private theorem zeroBodyLiteral (p : GroupedArgs) :
    (decorateAt p).bind (fun ms => markedSuccessorCode (bodyArgs (p,ms))) = zeroBodyCode p := rfl

theorem zeroBodyPrimitive : Primrec zeroBodyCode := by
  have body := exactRawMarkedSuccessorEffectivity.comp bodyArgsPrimitive
  exact (Primrec.option_bind decorateAtPrimitive body.to₂).of_eq zeroBodyLiteral

private theorem coefficientAtPrimitive :
    Primrec (fun p : GroupedArgs => coefficientCode p.2.1 p.2.2) := by
  have tape : Primrec (fun p : GroupedArgs => p.2.1) := Primrec.fst.comp Primrec.snd
  have answers : Primrec (fun p : GroupedArgs => p.2.2) := Primrec.snd.comp Primrec.snd
  exact coefficientPrimitive.comp tape answers

private theorem chooseZeroPrimitive {A X : Type} [Primcodable A] [Primcodable X]
    {coefficient : A → Int} {body : A → Option X}
    (coef : Primrec coefficient) (hbody : Primrec body) :
    Primrec (fun p => (coefficient p,if coefficient p = 0 then body p else none)) :=
  coef.pair (Primrec.ite (Primrec.eq.comp coef (Primrec.const 0)) hbody (Primrec.const none))

theorem groupedPrimitive : Primrec groupedCode :=
  (chooseZeroPrimitive coefficientAtPrimitive zeroBodyPrimitive).of_eq (fun _ => rfl)

private def groupSource (p : Args) : Option (List RawTerm) := groupCheckedRaw p.1 p.2.2.1

private theorem groupSourcePrimitive : Primrec groupSource := by
  have tape : Primrec (fun p : Args => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  exact groupCheckedRawPrimitive.comp Primrec.fst tape

private def withGroupedArgs (p : Args × List RawTerm) : GroupedArgs :=
  (p.1.2.1,p.2,p.1.2.2.2)

private theorem withGroupedArgsPrimitive : Primrec withGroupedArgs := by
  let A := Args × List RawTerm
  have base : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have c : Primrec (fun p : A => p.1.2.1) := Primrec.fst.comp base
  have answers : Primrec (fun p : A => p.1.2.2.2) := Primrec.snd.comp (Primrec.snd.comp base)
  exact c.pair (Primrec.snd.pair answers)

private theorem nodeLiteral (p : Args) :
    (groupSource p).map (fun tape => groupedCode (withGroupedArgs (p,tape))) = nodeCode p := by
  unfold nodeCode
  change (groupSource p).map (fun tape => groupedCode (withGroupedArgs (p,tape))) =
    (groupSource p).bind (fun tape => some (groupedCode (withGroupedArgs (p,tape))))
  cases groupSource p <;> rfl

theorem nodePrimitive : Primrec nodeCode := by
  have onGroup := groupedPrimitive.comp withGroupedArgsPrimitive
  exact (Primrec.option_map groupSourcePrimitive onGroup.to₂).of_eq nodeLiteral

theorem exactRawCanonicalNodeEffectivity : ExactRawCanonicalNodeEffectivity :=
  ⟨zeroBodyPrimitive,groupedPrimitive,nodePrimitive⟩

end LogicLineages.PermittedControl.ActualRawCanonicalNode
