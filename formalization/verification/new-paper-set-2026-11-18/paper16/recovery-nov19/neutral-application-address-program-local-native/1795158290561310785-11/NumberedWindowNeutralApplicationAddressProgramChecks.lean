module

public import LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationAddressProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramProof
import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
import LogicLineages.PersistentMarking.NumberedWindowAddressProgramProof
import LogicLineages.PersistentMarking.NumberedWindowScalarProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationAddressProgramChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowNeutralApplicationAddress NumberedWindowNeutralApplicationAddressProgramTargets
open NumberedWindowAddressAlgorithm (Address addressView)
open NumberedWindowAddressProgramProof (addressPrim)
open NumberedWindowFieldAlgorithm (pack packNode unpackNode)
open NumberedWindowMarkRootProgramProof (nodePrim readPrim)
open NumberedWindowPositivePathAlgorithm (RawEdge edgeView)
open NumberedWindowPositivePathParserPrograms (edgePrim)
open NumberedWindowScalarAlgorithm (Settings least)
open NumberedWindowScalarProgramProof (leastPrim)

private theorem packPrim : Primrec pack := by
  obtain ⟨p,h⟩ := NumberedWindowFieldProgramChecks.exact_OrderedFieldPrograms.1
  apply ((Proof.primitiveEvaluation 1 p).comp
    (Primrec.vector_cons.comp Primrec.encode (Primrec.const List.Vector.nil))).of_eq
  exact h

private abbrev Node := Nat × List Nat

private def select (tag arity index : Nat) (node : Node) : Option Nat :=
  if node.1 = tag ∧ node.2.length = arity then some (node.2.getD index 0) else none

private theorem selectPrim (tag arity index : Nat) : Primrec (select tag arity index) :=
  Primrec.ite ((Primrec.eq.comp Primrec.fst (Primrec.const tag)).and
    (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const arity)))
    (Primrec.option_some.comp ((Primrec.list_getD 0).comp Primrec.snd (Primrec.const index)))
    (Primrec.const none)

private theorem functionPrim : Primrec functionField := by
  apply ((Primrec.option_bind₁ (selectPrim 6 4 2)).comp readPrim).of_eq
  intro n
  cases h : unpackNode n with
  | none => rfl
  | some row =>
    rcases row with ⟨tag,fields⟩
    rcases tag with _ | _ | _ | _ | _ | _ | _ | tag <;>
      rcases fields with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,_ | ⟨e,tail⟩⟩⟩⟩⟩ <;>
      simp [functionField,h,select,List.getD_eq_getElem?_getD]

private theorem childPrim : Primrec functionChild := by
  apply ((Primrec.option_bind₁ (selectPrim 5 1 0)).comp readPrim).of_eq
  intro n
  cases h : unpackNode n with
  | none => rfl
  | some row =>
    rcases row with ⟨tag,fields⟩
    rcases tag with _ | _ | _ | _ | _ | _ | tag <;>
      rcases fields with _ | ⟨a,_ | ⟨b,tail⟩⟩ <;>
      simp [functionChild,h,select,List.getD_eq_getElem?_getD]

private abbrev Children := Nat × Nat × Nat

private def children (p : RawEdge) : Option Children := do
  let q ← functionField p.1
  let r ← functionField p.2.2
  (functionChild p.2.1).map (fun child => (q,r,child))

private theorem childrenPrim : Primrec children := by
  let Left := RawEdge × Nat
  let Both := Left × Nat
  let Full := Both × Nat
  have target : Primrec (fun p : Left => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have child : Primrec (fun p : Both => p.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have q : Primrec (fun p : Full => p.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have r : Primrec (fun p : Full => p.1.2) := Primrec.snd.comp Primrec.fst
  have output := q.pair (r.pair (Primrec.snd : Primrec (Prod.snd : Full → Nat)))
  have last := Primrec.option_map (childPrim.comp child) output.to₂
  have right := Primrec.option_bind (functionPrim.comp target) last.to₂
  exact Primrec.option_bind (functionPrim.comp Primrec.fst) right.to₂

private def build (s : Settings) (p : Address × Children) : Option (Nat × Nat) :=
  (least s p.1.1 p.1.2.1 p.2.2.1).map (fun k =>
    (packNode 3 [pack p.1.1,p.1.2.1,k],packNode 1 [p.2.1,p.2.2.1,p.2.2.2]))

private theorem buildPrim (s : Settings) : Primrec (build s) := by
  let I := Address × Children
  let E := I × Nat
  have context : Primrec (fun p : I => p.1.1) := Primrec.fst.comp Primrec.fst
  have ty : Primrec (fun p : I => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have q : Primrec (fun p : I => p.2.1) := Primrec.fst.comp Primrec.snd
  have r : Primrec (fun p : I => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have w : Primrec (fun p : I => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have previous := (leastPrim s).comp (context.pair (ty.pair r))
  have address := nodePrim.comp (Primrec.const 3) (Primrec.list_cons.comp
    (packPrim.comp (context.comp (Primrec.fst : Primrec (Prod.fst : E → I))))
    (Primrec.list_cons.comp (ty.comp Primrec.fst) (Primrec.list_cons.comp Primrec.snd (Primrec.const []))))
  have certificate := nodePrim.comp (Primrec.const 1) (Primrec.list_cons.comp (q.comp Primrec.fst)
    (Primrec.list_cons.comp (r.comp Primrec.fst) (Primrec.list_cons.comp (w.comp Primrec.fst) (Primrec.const []))))
  exact Primrec.option_map previous (address.pair certificate).to₂

private theorem witnessPrim (s : Settings) : Primrec₂ (functionWitness s) := by
  let Input := Nat × Nat
  let Found := Input × Address
  let Decoded := Found × RawEdge
  let Ready := Decoded × Children
  have cert : Primrec (fun p : Found => p.1.2) := Primrec.snd.comp Primrec.fst
  have a : Primrec (fun p : Ready => p.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have buildFrom := (buildPrim s).comp (a.pair Primrec.snd)
  have assembled := Primrec.option_bind (childrenPrim.comp (Primrec.snd : Primrec (Prod.snd : Decoded → RawEdge)))
    buildFrom.to₂
  have decoded := Primrec.option_bind (edgePrim.comp cert) assembled.to₂
  apply (Primrec.option_bind (addressPrim.comp (Primrec.fst : Primrec (Prod.fst : Input → Nat)))
    decoded.to₂).to₂.of_eq
  intro source certificate
  change ((addressView source).bind fun addr =>
    (edgeView certificate).bind fun edge => (children edge).bind fun fields => build s (addr,fields)) = _
  unfold functionWitness
  cases h : addressView source with
  | none => simp [h]
  | some addr =>
    rcases addr with ⟨ctx,ty,raw⟩
    cases ev : edgeView certificate with
    | none => simp [h,ev]
    | some row =>
      rcases row with ⟨q,w,r⟩
      cases qf : functionField q with
      | none => simp [children,h,ev,qf]
      | some q' =>
        cases rf : functionField r with
        | none => simp [children,h,ev,qf,rf]
        | some r' =>
          cases wf : functionChild w with
          | none => simp [children,h,ev,qf,rf,wf]
          | some w' =>
            cases done : least s ctx ty r' <;>
              simp [children,build,h,ev,qf,rf,wf,done]

theorem exact_NeutralFunctionWitnessProgram : NeutralFunctionWitnessProgram := by
  intro s
  let V := List.Vector Nat 2
  have source : Primrec (fun v : V => v.head) := Primrec.vector_head
  have tail : Primrec (fun v : V => v.tail) := Primrec.vector_tail
  have certificate := Primrec.vector_head.comp tail
  obtain ⟨p,h⟩ := Proof.allPrimitiveFunctions 2 _
    (Primrec.encode.comp ((witnessPrim s).comp source certificate))
  exact ⟨p,fun source certificate => h (source ::ᵥ certificate ::ᵥ nil)⟩

#print axioms exact_NeutralFunctionWitnessProgram

end LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationAddressProgramChecks
