module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionFrameConstructorsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionFrameQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStackComposition
open InternalApplicationResultStackCompositionFrameSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def q0 : Program 6 :=
  .composition InternalListCodec.headCode (fun _ : Fin 1 => (.projection 0))
def q1 : Program 6 :=
  .composition InternalListCodec.tailCode (fun _ : Fin 1 => (.projection 0))
def q2 : Program 6 :=
  .composition InternalUnpair.left (fun _ : Fin 1 => (q0))
def q3 : Program 6 :=
  .composition InternalUnpair.right (fun _ : Fin 1 => (q0))
def q4 : Program 6 :=
  .composition InternalUnpair.right (fun _ : Fin 1 => (q3))
def q5 : Program 6 :=
  .composition InternalUnpair.left (fun _ : Fin 1 => (q3))
def q6 : Program 6 :=
  .composition InternalUnpair.left (fun _ : Fin 1 => (q4))
def q7 : Program 6 :=
  .composition InternalUnpair.right (fun _ : Fin 1 => (q4))
def q8 : Program 6 :=
  .composition InternalUnpair.left (fun _ : Fin 1 => (q7))
def q9 : Program 6 :=
  .composition InternalUnpair.right (fun _ : Fin 1 => (q7))
def q10 : Program 6 :=
  .composition InternalUnpair.left (fun _ : Fin 1 => (q9))
def q11 : Program 6 :=
  .composition InternalUnpair.right (fun _ : Fin 1 => (q9))
def q12 (leaf : Program 1) : Program 6 :=
  .composition leaf (fun _ : Fin 1 => (q3))
def q13 (mw : Bool) : Program 6 :=
  .composition (extend mw) ![(q1),(.projection 2)]
def q14 : Program 6 :=
  .composition InternalListCodec.consCode ![(q8),(q5)]
def q15 : Program 6 :=
  .composition InternalPairing.pairing ![(q14),(q10)]
def q16 : Program 6 :=
  .composition InternalPairing.pairing ![(q8),(q11)]
def q17 : Program 6 :=
  .composition InternalPairing.pairing ![(InternalAcceptance.constantZero 6),(q15)]
def q18 : Program 6 :=
  .composition InternalPairing.pairing ![(InternalAcceptance.constantZero 6),(q16)]
def q19 : Program 6 :=
  .composition InternalPairing.pairing ![(q8),(q5)]
def q20 : Program 6 :=
  .composition InternalPairing.pairing ![(InternalLessThan.constantOne 6),(q19)]
def q21 : Program 6 :=
  .composition InternalListCodec.consCode ![(q20),(q1)]
def q22 : Program 6 :=
  .composition InternalListCodec.consCode ![(q18),(q21)]
def q23 : Program 6 :=
  .composition InternalListCodec.consCode ![(q17),(q22)]
def q24 (mw : Bool) : Program 6 :=
  .composition InternalListCodec.consCode ![(q20),(q13 mw)]
def q25 (mw : Bool) : Program 6 :=
  .composition InternalListCodec.consCode ![(q18),(q24 mw)]
def q26 (mw : Bool) : Program 6 :=
  .composition InternalListCodec.consCode ![(q17),(q25 mw)]
def q27 (leaf : Program 1) : Program 6 :=
  .composition InternalListCodec.consCode ![(q12 leaf),(.projection 1)]
def q28 (leaf : Program 1) : Program 6 :=
  .composition InternalListCodec.consCode ![(q12 leaf),(.projection 5)]
def q29 (leaf : Program 1) : Program 6 :=
  .composition liveState ![(q1),(q27 leaf)]
def q30 (mw : Bool) (leaf : Program 1) : Program 6 :=
  .composition liveState ![(q13 mw),(q28 leaf)]
def q31 : Program 6 :=
  .composition liveState ![(q23),(.projection 1)]
def q32 (mw : Bool) : Program 6 :=
  .composition liveState ![(q26 mw),(.projection 5)]
def q33 : Program 6 :=
  .composition InternalListCodec.headCode (fun _ : Fin 1 => (.projection 1))
def q34 : Program 6 :=
  .composition InternalListCodec.tailCode (fun _ : Fin 1 => (.projection 1))
def q35 : Program 6 :=
  .composition InternalListCodec.headCode (fun _ : Fin 1 => (q34))
def q36 : Program 6 :=
  .composition InternalListCodec.tailCode (fun _ : Fin 1 => (q34))
def q37 (combine : Program 4) : Program 6 :=
  .composition combine ![(q5),(q4),(q35),(q33)]
def q38 (mr : Bool) : Program 6 :=
  .composition (extend mr) ![(q36),(.projection 3)]
def q39 (mr : Bool) : Program 6 :=
  .composition (extend mr) ![(q34),(.projection 3)]
def q40 (combine : Program 4) : Program 6 :=
  .composition InternalListCodec.consCode ![(q37 combine),(q36)]
def q41 (mr : Bool) (combine : Program 4) : Program 6 :=
  .composition InternalListCodec.consCode ![(q37 combine),(q38 mr)]
def q42 (combine : Program 4) : Program 6 :=
  .composition liveState ![(q1),(q40 combine)]
def q43 (mw : Bool) (mr : Bool) (combine : Program 4) : Program 6 :=
  .composition liveState ![(q13 mw),(q41 mr combine)]

def queries (mw mr : Bool) (leaf : Program 1) (combine : Program 4) : Fin 44 → Program 6 :=
  ![q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11,q12 leaf,q13 mw,q14,q15,q16,q17,q18,q19,q20,q21,q22,q23,q24 mw,q25 mw,q26 mw,q27 leaf,q28 leaf,q29 leaf,q30 mw leaf,q31,q32 mw,q33,q34,q35,q36,q37 combine,q38 mr,q39 mr,q40 combine,q41 mr combine,q42 combine,q43 mw mr combine]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionFrameQueryProof
