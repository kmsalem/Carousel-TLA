---- MODULE MC ----
EXTENDS carousel, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_1539885832116242000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1NumOfMessages
const_1539885832116243000 == 
6
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1539885832116244000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1539885832116245000 ==
StatusInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1539885832116246000 ==
CounterInvariant
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1539885832116247000 ==
Termination
----
=============================================================================
\* Modification History
\* Created Thu Oct 18 14:03:52 EDT 2018 by dzklavier
