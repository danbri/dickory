import L4Factoidal.Dataflow.Stage
import Policy

/- Native integration against the Factoidal source commit pinned by the npm
runtime. The browser does not import these native compiled modules. -/
namespace LinkedAssurance
open L4Factoidal.Dataflow

structure AdapterInput where
  context : Context
  execution : Execution
  bindings : List QueryBinding
  observations : List QueryObservation

/-- This is Factoidal's existing Stage type, not a parallel pipeline model. -/
def evidenceAdapterStage : Stage String AdapterInput Evidence where
  run i := adaptEvidence i.context i.execution i.bindings i.observations
  contract i e := adapterRequirements i.context i.execution i.bindings i.observations e
  sound i e h := adaptEvidence_contract i.context i.execution i.bindings i.observations e h

def checkedPolicyStage (s : OperationalState) : Stage String Evidence Decision :=
  Stage.ofFun (fun e => policy e s)
    (fun e d => d = .permit → permitRequirements e s)
    (fun e h => policy_contract e s h)

def adaptedPolicyStage (s : OperationalState) : Stage String AdapterInput Decision :=
  evidenceAdapterStage.comp (checkedPolicyStage s)

theorem adaptedPolicyStage_sound (s : OperationalState) (i : AdapterInput) (d : Decision)
    (h : (adaptedPolicyStage s).run i = .ok d) :
    ∃ e, adapterRequirements i.context i.execution i.bindings i.observations e ∧
      (d = .permit → permitRequirements e s) :=
  (adaptedPolicyStage s).sound i d h

#print axioms adaptedPolicyStage_sound
end LinkedAssurance
