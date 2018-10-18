---- MODULE MC ----
EXTENDS carousel, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_1539885325275236000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1NumOfMessages
const_1539885325275237000 == 
6
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1539885325275238000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1539885325275239000 ==
StatusInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1539885325275240000 ==
CounterInvariant
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1539885325275241000 ==
Termination
----
=============================================================================
\* Modification History
\* Created Thu Oct 18 13:55:25 EDT 2018 by dzklavier
