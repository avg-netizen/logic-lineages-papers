module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftEdgeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructors
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Composition abbreviations for the already calibrated ORIGINAL Nat.pair,
Nat.unpair and source-list constructor programs. -/
def pairOf {n : Nat} (p q : Program n) : Program n :=
  .composition InternalPairing.pairing ![p,q]

def leftOf {n : Nat} (p : Program n) : Program n :=
  .composition InternalUnpair.left (fun _ : Fin 1 => p)

def rightOf {n : Nat} (p : Program n) : Program n :=
  .composition InternalUnpair.right (fun _ : Fin 1 => p)

def consOf {n : Nat} (p q : Program n) : Program n :=
  .composition InternalListCodec.consCode ![p,q]

def two (n : Nat) : Program n :=
  .composition .succ (fun _ : Fin 1 => InternalLessThan.constantOne n)

/-- The original raw application node on its two unpaired payloads.
Inputs are [domain,codomain,functionPayload,argumentPayload]. -/
def packedApplication : Program 4 :=
  pairOf (.projection 1) (pairOf (two 4)
    (pairOf (.projection 0) (pairOf (.projection 2) (.projection 3))))

/-- The exact original raw constructor, including its off-domain behavior.
It discards only the two outer type fields, as rawApplication does. -/
def application : Program 4 :=
  .composition packedApplication
    ![.projection 0,.projection 1,rightOf (.projection 2),rightOf (.projection 3)]

/-- The original appFunction position has number Nat.pair 1 0 = 2.
The prefix is the unchanged original list cons, not a fresh path encoding. -/
def prefixedPath : Program 1 := consOf (two 1) InternalUnpair.left

def stepLift : Program 1 := pairOf prefixedPath InternalUnpair.right

/-- Exactly source paired with (target paired with step). -/
def edgeCode : Program 3 :=
  pairOf (.projection 0) (pairOf (.projection 1) (.projection 2))

def source : Program 1 := InternalUnpair.left
def target : Program 1 := leftOf InternalUnpair.right
def step : Program 1 := rightOf InternalUnpair.right

/-- Read the certificate coordinate of [domain,codomain,argument,certificate]. -/
def certificateField (p : Program 1) : Program 4 :=
  .composition p (fun _ : Fin 1 => .projection 3)

def sourceApplication : Program 4 :=
  .composition application
    ![.projection 0,.projection 1,certificateField source,.projection 2]

def targetApplication : Program 4 :=
  .composition application
    ![.projection 0,.projection 1,certificateField target,.projection 2]

def liftedStep : Program 4 :=
  .composition stepLift (fun _ : Fin 1 => certificateField step)

/-- The explicit original edge transformer. No primitive-recursive witness
is selected by a representability or semantic-calibration theorem. -/
def edgeLift : Program 4 :=
  .composition edgeCode ![sourceApplication,targetApplication,liftedStep]

abbrev graph1 {α : Type} (p : Program 1) (out x : OTerm α) : Formula α :=
  programGraph p out (Fin.cons x Fin.elim0)

abbrev graph2 {α : Type} (p : Program 2) (out x y : OTerm α) : Formula α :=
  programGraph p out (Fin.cons x (Fin.cons y Fin.elim0))

abbrev graph3 {α : Type} (p : Program 3) (out x y z : OTerm α) : Formula α :=
  programGraph p out (Fin.cons x (Fin.cons y (Fin.cons z Fin.elim0)))

abbrev graph4 {α : Type} (p : Program 4) (out w x y z : OTerm α) : Formula α :=
  programGraph p out (Fin.cons w (Fin.cons x (Fin.cons y (Fin.cons z Fin.elim0))))

def positionTerm {α : Type} : OTerm α :=
  numeral (NumberedNumericStep.positionNumber .appFunction)

def selectors {α : Type} (certificate s t k : OTerm α) : Formula α :=
  graph1 source s certificate ⊓
    (graph1 target t certificate ⊓ graph1 step k certificate)

/-- All four supplied original graph witnesses share the same raw fields. -/
def liftPremises {α : Type} (d e a certificate s t k s' t' k' : OTerm α) : Formula α :=
  graph3 edgeCode certificate s t k ⊓
    (graph4 application s' d e s a ⊓
      (graph4 application t' d e t a ⊓ graph1 stepLift k' k))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructors
