module

public import LogicLineages.PersistentMarking.NumberedWindowRawContextFramePrograms
import LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawContextProgramProof
open LogicLineages.ComputabilityKnowledge NumberedWindowRawContextAlgorithm
open NumberedWindowRawContextProgramTargets NumberedWindowRawContextFramePrograms

private def dispatch (root : RawRoot) (p : Node × Frame) : State :=
  if p.1.1 = 0 ∧ p.1.2.length = 1 then
    (root p.2.1 (p.1.2.getD 0 0) p.2.2.2,none)
  else (false,next p.1.1 p.1.2 p.2.1 p.2.2.2)

private theorem dispatchPrim {root : RawRoot}
    (hr : Primrec (fun p : Frame => root p.1 p.2.1 p.2.2)) : Primrec (dispatch root) := by
  let P := Node × Frame
  have nd : Primrec (Prod.fst : P → Node) := Primrec.fst
  have tag := Primrec.fst.comp nd
  have fs := Primrec.snd.comp nd
  have valid := (Primrec.eq.comp tag (Primrec.const 0)).and
    (Primrec.eq.comp (Primrec.list_length.comp fs) (Primrec.const 1))
  have q : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have r : Primrec (fun p : P => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have payload := (Primrec.list_getD 0).comp fs (Primrec.const 0)
  exact Primrec.ite valid ((hr.comp (q.pair (payload.pair r))).pair (Primrec.const none))
    ((Primrec.const false).pair nextPrim)

private def process (root : RawRoot) (p : Frame) : State :=
  ((NumberedWindowFieldAlgorithm.unpackNode p.2.1).map (fun v => dispatch root (v,p))).getD (false,none)

private theorem processPrim {root : RawRoot}
    (hr : Primrec (fun p : Frame => root p.1 p.2.1 p.2.2)) : Primrec (process root) :=
  Primrec.option_getD.comp (Primrec.option_map (nodesPrim.comp (Primrec.fst.comp Primrec.snd))
    ((dispatchPrim hr).comp (Primrec.snd.pair Primrec.fst)).to₂) (Primrec.const (false,none))

private theorem tickPrim {root : RawRoot}
    (hr : Primrec (fun p : Frame => root p.1 p.2.1 p.2.2)) : Primrec (tick root) := by
  apply (Primrec.option_getD.comp
    (Primrec.option_map (Primrec.snd : Primrec (Prod.snd : State → Option Frame))
      ((processPrim hr).comp Primrec.snd).to₂) Primrec.id).of_eq
  rintro ⟨b,_ | ⟨q,w,r⟩⟩
  · rfl
  · cases h : NumberedWindowFieldAlgorithm.unpackNode w with
    | none => simp [tick,process,h]
    | some node =>
      rcases node with ⟨_ | tag,ws⟩
      · rcases ws with _ | ⟨p,_ | ⟨x,tail⟩⟩ <;> simp [tick,process,dispatch,h,List.getD_eq_getElem?_getD]
      · simp [tick,process,dispatch,h]

private theorem tickIterate (root : RawRoot) (n : Nat) (s : State) :
    tick root (iterate root n s) = iterate root n (tick root s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih (tick root s)

private theorem iteratePrim {root : RawRoot}
    (hr : Primrec (fun p : Frame => root p.1 p.2.1 p.2.2)) :
    Primrec (fun p : State × Nat => iterate root p.2 p.1) := by
  have update : Primrec₂ (fun (_ : State) (p : Nat × State) => tick root p.2) :=
    (tickPrim hr).comp (Primrec.snd.comp Primrec.snd)
  change Primrec₂ (fun st n => iterate root n st)
  apply (Primrec.nat_rec Primrec.id update).of_eq
  intro s n
  induction n with
  | zero => rfl
  | succ n ih =>
    change tick root _ = iterate root (n+1) s
    exact (congrArg (tick root) ih).trans (tickIterate root n s)

private theorem rawPrim {root : RawRoot}
    (hr : Primrec (fun p : Frame => root p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Frame => raw root p.1 p.2.1 p.2.2) := by
  have q : Primrec (fun p : Frame => p.1) := Primrec.fst
  have w : Primrec (fun p : Frame => p.2.1) := Primrec.fst.comp Primrec.snd
  have r : Primrec (fun p : Frame => p.2.2) := Primrec.snd.comp Primrec.snd
  have syntaxCheck := Primrec.fst.comp NumberedWindowSyntaxProgramProof.bits
  have init := (Primrec.const false).pair (Primrec.option_some : Primrec (some : Frame → Option Frame))
  have run := Primrec.fst.comp ((iteratePrim hr).comp (init.pair w))
  exact Primrec.and.comp (Primrec.and.comp (syntaxCheck.comp q) (syntaxCheck.comp r)) run

theorem windowStepPrim {root : RawRoot} {window : Window}
    (hr : Primrec (fun p : Frame => root p.1 p.2.1 p.2.2))
    (hw : Primrec (fun p : WindowInput => window p.1 p.2.1 p.2.2)) :
    Primrec (fun p : StepInput => windowStep root window p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have ctx : Primrec (fun p : StepInput => p.1) := Primrec.fst
  have ty : Primrec (fun p : StepInput => p.2.1) := Primrec.fst.comp Primrec.snd
  have q : Primrec (fun p : StepInput => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have r : Primrec (fun p : StepInput => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have rawCheck := (rawPrim hr).comp (Primrec.snd.comp Primrec.snd : Primrec (fun p : StepInput => p.2.2))
  exact Primrec.and.comp
    (Primrec.and.comp rawCheck (hw.comp (ctx.pair (ty.pair q)))) (hw.comp (ctx.pair (ty.pair r)))

theorem program : ContextualStepProgram := by
  intro root window hr hw
  let read (n : Nat) := (Encodable.decode (α := StepInput) n).getD default
  have readPrim : Primrec read := Primrec.option_getD.comp Primrec.decode (Primrec.const default)
  have numeric := Primrec.ite (Primrec.eq.comp (windowStepPrim hr hw) (Primrec.const true))
    (Primrec.const (1 : Nat)) (Primrec.const 0)
  obtain ⟨p,hp⟩ := (GorbowPRProgram.Proof.unaryCorrespondence _).mp (numeric.comp readPrim)
  refine ⟨p,?_⟩
  intro ctx ty q w r
  let data : StepInput := (ctx,ty,q,w,r)
  have round : read (Encodable.encode data) = data := by
    change ((Encodable.decode (Encodable.encode data) : Option StepInput).getD default) = data
    simp only [Encodable.encodek,Option.getD_some]
  have he := hp (Encodable.encode data)
  rw [round] at he
  exact he

end LogicLineages.PersistentMarking.NumberedWindowRawContextProgramProof
